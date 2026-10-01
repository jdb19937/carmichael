"""Sortie ZBV2 helpers (BVL2 continued: the sigma extension by discrete Abel
summation, mCheckQ, the phiSig block, the diagonalisation)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbvlib import *
from lin import linarith, nlinarith, lineq

# ---- the standing expressions of the sigma extension
HY = '( Y e. RR /\\ 1 <_ Y )'
HS = '( S e. RR /\\ 1 <_ S )'
HYS = '( %s /\\ %s )' % (HY, HS)
E = '( S - 1 )'
NE = '-u ( S - 1 )'
MU = lambda n: '( mmu ` %s )' % n
MQ = lambda n: '( ( mmu ` %s ) / %s )' % (n, n)
CX = lambda x: '( %s ^c -u %s )' % (x, E)               # x ^c -u E
LG = lambda x: '( log ` ( Y / %s ) )' % x               # log ( Y / x )
G = lambda x: '( %s x. %s )' % (CX(x), LG(x))           # the kernel g(x)
H = lambda x: '( %s x. ( 1 + ( %s x. %s ) ) )' % (CX(x), E, LG(x))   # h(x) = -x g'(x)
ELL = lambda k: '( log ` ( ( %s + 1 ) / %s ) )' % (k, k)             # the log gap
P1 = lambda k: '( %s + 1 )' % k
R = lambda k: '( ( %s - %s ) / %s )' % (G(k), G(P1(k)), ELL(k))       # the chord slope
CS = lambda x, m: 'sum_ n e. ( 1 ... %s ) ( %s x. ( log ` ( %s / n ) ) )' % (m, MQ('n'), x)
AS = lambda m: 'sum_ n e. ( 1 ... %s ) %s' % (m, MQ('n'))
NY = '( |_ ` Y )'
TERM = lambda n: '( ( ( mmu ` %s ) x. ( %s ^c -u S ) ) x. ( log ` ( Y / %s ) ) )' % (n, n, n)
SUMY = 'sum_ n e. ( 1 ... %s ) %s' % (NY, TERM('n'))
M113 = '( ; 1 1 / 3 )'
BOUND = '( %s x. ( 1 + ( ( S - 1 ) x. ( log ` Y ) ) ) )' % M113


def ysfacts(w, ante, hys):
    """from hys: ( ante -> HYS ): Y e. RR, 1 <_ Y, Y e. RR+, S e. RR, 1 <_ S, E e. RR, 0 <_ E, -u E e. RR"""
    st = mkst(w, ante)
    hy = st([hys], 'simpld', HY); hs = st([hys], 'simprd', HS)
    yr = st([hy], 'simpld', 'Y e. RR'); y1 = st([hy], 'simprd', '1 <_ Y')
    yrp = st([yr, linarith(w, ante, [y1], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+')
    sr = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 <_ S')
    er = st([sr, st([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % E)
    e0 = linarith(w, ante, [s1], '0 <_ %s' % E, leaves={'S': sr})
    ner = st([er], 'renegcld', '%s e. RR' % NE)
    return dict(hy=hy, hs=hs, yr=yr, y1=y1, yrp=yrp, sr=sr, s1=s1, er=er, e0=e0, ner=ner,
                ec=st([er], 'recnd', '%s e. CC' % E))


def kfacts(w, ante, knn, k):
    """closures for an index k e. NN under ante (step knn): RR+, RR, CC, =/= 0, k + 1 e. NN, RR+, RR, CC"""
    st = mkst(w, ante)
    krp = st([knn], 'nnrpd', '%s e. RR+' % k)
    kre = st([krp], 'rpred', '%s e. RR' % k); kcc = st([krp], 'rpcnd', '%s e. CC' % k); kne = st([krp], 'rpne0d', '%s =/= 0' % k)
    k1nn = st([knn], 'peano2nnd', '%s e. NN' % P1(k))
    k1rp = st([k1nn], 'nnrpd', '%s e. RR+' % P1(k))
    k1re = st([k1rp], 'rpred', '%s e. RR' % P1(k)); k1cc = st([k1rp], 'rpcnd', '%s e. CC' % P1(k))
    return dict(nn=knn, rp=krp, re=kre, cc=kcc, ne=kne, p1nn=k1nn, p1rp=k1rp, p1re=k1re, p1cc=k1cc)


def cxfacts(w, ante, krp, ner, k):
    """( k ^c -u E ) e. RR+, RR, CC, 0 <_ from k e. RR+ (krp) and -u E e. RR (ner)"""
    st = mkst(w, ante)
    rp = st([krp, ner], 'rpcxpcld', '%s e. RR+' % CX(k))
    re = st([rp], 'rpred', '%s e. RR' % CX(k))
    return dict(rp=rp, re=re, cc=st([rp], 'rpcnd', '%s e. CC' % CX(k)), ge0=st([rp], 'rpge0d', '0 <_ %s' % CX(k)))


def lgfacts(w, ante, yrp, krp, k):
    """( Y / k ) e. RR+, ( log ` ( Y / k ) ) e. RR, CC"""
    st = mkst(w, ante)
    qrp = st([yrp, krp], 'rpdivcld', '( Y / %s ) e. RR+' % k)
    lr = st([qrp], 'relogcld', '%s e. RR' % LG(k))
    return dict(qrp=qrp, re=lr, cc=st([lr], 'recnd', '%s e. CC' % LG(k)))


def ellfacts(w, ante, kf, k):
    """ELL(k) e. RR+, RR, CC, =/= 0 from the kfacts dict kf"""
    st = mkst(w, ante)
    qrp = st([kf['p1rp'], kf['rp']], 'rpdivcld', '( %s / %s ) e. RR+' % (P1(k), k))
    qre = st([qrp], 'rpred', '( %s / %s ) e. RR' % (P1(k), k))
    # 1 < ( k + 1 ) / k  <->  k < k + 1
    lt = st([kf['re']], 'ltp1d', '%s < %s' % (k, P1(k)))
    bi = st([st([], '1red', '1 e. RR'), kf['p1re'], kf['rp']], 'ltmuldivd', '( ( 1 x. %s ) < %s <-> 1 < ( %s / %s ) )' % (k, P1(k), P1(k), k))
    lt2 = st([st([st([kf['cc']], 'mullidd', '( 1 x. %s ) = %s' % (k, k)), lt], 'eqbrtrd', '( 1 x. %s ) < %s' % (k, P1(k))), bi], 'mpbid',
             '1 < ( %s / %s )' % (P1(k), k))
    rp = sy2(w, ante, qre, lt2, 'rplogcl', '%s e. RR+' % ELL(k))
    re = st([rp], 'rpred', '%s e. RR' % ELL(k))
    return dict(qrp=qrp, rp=rp, re=re, cc=st([re], 'recnd', '%s e. CC' % ELL(k)), ne=st([rp], 'rpne0d', '%s =/= 0' % ELL(k)),
                gt0=st([rp], 'rpgt0d', '0 < %s' % ELL(k)))


def mqfacts(w, ante, knn, k):
    """( mmu ` k ) e. ZZ, RR, CC and ( ( mmu ` k ) / k ) e. RR, CC from k e. NN"""
    st = mkst(w, ante)
    muz = sy(w, ante, knn, 'mucl', '%s e. ZZ' % MU(k))
    mur = st([muz], 'zred', '%s e. RR' % MU(k)); muc = st([mur], 'recnd', '%s e. CC' % MU(k))
    krp = st([knn], 'nnrpd', '%s e. RR+' % k)
    mqr = st([mur, krp], 'rerpdivcld', '%s e. RR' % MQ(k))
    return dict(muz=muz, mur=mur, muc=muc, mqr=mqr, mqc=st([mqr], 'recnd', '%s e. CC' % MQ(k)))


def _topeq(f):
    """split a class equation A = B at its top-level ' = ' (parenthesis depth 0)"""
    toks = f.split(); d = 0
    for i, t in enumerate(toks):
        if t == '(':
            d += 1
        elif t == ')':
            d -= 1
        elif t == '=' and d == 0:
            return ' '.join(toks[:i]), ' '.join(toks[i + 1:])
    raise ValueError('no top-level = in ' + f)


def eqtr(w, ante, steps, final):
    """chain equality steps ( ante -> A = B ), ( ante -> B = C ), ... by eqtrd"""
    from cl import formula_of, strip_ante
    cur = steps[0]
    for s in steps[1:]:
        a = strip_ante(formula_of(w, cur), ante); b = strip_ante(formula_of(w, s), ante)
        lhs = _topeq(a)[0]; rhs = _topeq(b)[1]
        cur = w.s([cur, s], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, rhs))
    return cur


# ---- section 1 (bvmchks): the frozen statements, one place, so that the
# blueprint, the grammar check and the generators cannot drift apart.
HK = lambda k: '( %s e. NN /\\ ( %s + 1 ) <_ Y )' % (k, k)          # K e. NN /\ ( K + 1 ) <_ Y
HK2 = lambda k: '( %s e. NN /\\ ( ( %s + 1 ) + 1 ) <_ Y )' % (k, k)
ANTE_CH = ('( ( ( Q e. RR /\\ 0 <_ Q ) /\\ ( E e. RR /\\ 0 <_ E ) /\\ ( U e. RR /\\ 0 <_ U ) ) /\\ '
           '( ( T e. RR /\\ U <_ T ) /\\ ( ( 1 - Q ) <_ ( E x. U ) /\\ ( Q x. ( E x. U ) ) <_ ( 1 - Q ) ) ) )')
CHORD_L = '( %s x. %s ) <_ ( %s - %s )' % (H(P1('K')), ELL('K'), G('K'), G(P1('K')))
CHORD_R = '( %s - %s ) <_ ( %s x. %s )' % (G('K'), G(P1('K')), H('K'), ELL('K'))
SUMN = lambda m: 'sum_ n e. ( 1 ... %s ) %s' % (m, TERM('n'))
# the generic Abel lemmas: A, G, R, L, F are function variables; sums bind n and i
FA = lambda x: '( A ` %s )' % x
FG = lambda x: '( G ` %s )' % x
FR = lambda x: '( R ` %s )' % x
FL = lambda x: '( L ` %s )' % x
FF = lambda x: '( F ` %s )' % x
ASA = lambda m: 'sum_ n e. ( 1 ... %s ) %s' % (m, FA('n'))
SABEL = 'sum_ n e. ( 1 ... N ) ( %s x. ( %s - %s ) )' % (FA('n'), FG('n'), FG('( N + 1 )'))
SSWAP = 'sum_ i e. ( 1 ... N ) ( ( %s - %s ) x. %s )' % (FG('i'), FG('( i + 1 )'), ASA('i'))
SPARTS = 'sum_ i e. ( 1 ... N ) ( %s x. ( %s - %s ) )' % (FR('i'), FF('( i + 1 )'), FF('i'))
SDIFF = 'sum_ i e. ( 1 ..^ N ) ( ( %s - %s ) x. %s )' % (FR('i'), FR('( i + 1 )'), FF('( i + 1 )'))
RN1 = '( %s - %s )' % (FR('1'), 'P')

STATEMENTS = {
    'bvefge1p': '( ( A e. RR /\\ 0 <_ A ) -> ( 1 + A ) <_ ( exp ` A ) )',
    'bvexpl1': '( ( A e. RR /\\ 0 <_ A ) -> ( 1 - ( exp ` -u A ) ) <_ A )',
    'bvexpl2': '( ( A e. RR /\\ 0 <_ A ) -> ( ( exp ` -u A ) x. A ) <_ ( 1 - ( exp ` -u A ) ) )',
    'bvchordlem2': '( %s -> ( ( Q x. ( 1 + ( E x. ( T - U ) ) ) ) x. U ) <_ ( T - ( Q x. ( T - U ) ) ) )' % ANTE_CH,
    'bvchordlem3': '( %s -> ( T - ( Q x. ( T - U ) ) ) <_ ( ( 1 + ( E x. T ) ) x. U ) )' % ANTE_CH,
    'bvchordlem4': '( ( %s /\\ K e. NN ) -> %s = ( %s x. ( exp ` -u ( %s x. %s ) ) ) )' % (HS, CX(P1('K')), CX('K'), E, ELL('K')),
    'bvchord': '( ( %s /\\ %s ) -> ( %s /\\ %s ) )' % (HYS, HK('K'), CHORD_L, CHORD_R),
    'bvrlow': '( ( %s /\\ %s ) -> %s <_ %s )' % (HYS, HK('K'), H(P1('K')), R('K')),
    'bvrfirst': '( ( %s /\\ %s ) -> %s <_ %s )' % (HYS, HK('K'), R('K'), H('K')),
    'bvrlast': '( ( %s /\\ %s ) -> %s <_ %s )' % (HYS, HK('K'), CX(P1('K')), R('K')),
    'bvrmono': '( ( %s /\\ %s ) -> %s <_ %s )' % (HYS, HK2('K'), R(P1('K')), R('K')),
    'bvcshift': '( ( ( X e. RR+ /\\ Z e. RR+ ) /\\ K e. NN ) -> %s = ( %s + ( ( log ` ( X / Z ) ) x. %s ) ) )' % (CS('X', 'K'), CS('Z', 'K'), AS('K')),
    'bvcp1': '( K e. NN -> %s = ( %s + ( %s x. %s ) ) )' % (CS(P1('K'), P1('K')), CS('K', 'K'), ELL('K'), AS('K')),
    'bvc1': '%s = 0' % CS('1', '1'),
    'bvabellem1': '( ph -> %s = %s )' % (SABEL, SSWAP),
    'bvabellem2': '( ph -> %s = ( %s + ( ( %s x. %s ) - ( %s x. %s ) ) ) )' % (SPARTS, SDIFF, FR('N'), FF('( N + 1 )'), FR('1'), FF('1')),
    'bvabellem3': '( ph -> ( %s - ( P x. %s ) ) = ( %s + ( ( %s - P ) x. %s ) ) )' % (SABEL, FF('( N + 1 )'), SDIFF, FR('N'), FF('( N + 1 )')),
    'bvabelin': '( ph -> ( abs ` ( %s - ( P x. %s ) ) ) <_ ( M x. %s ) )' % (SABEL, FF('( N + 1 )'), RN1),
    'bvmchkslem1': '( ( %s /\\ K e. NN ) -> %s = ( %s x. %s ) )' % (HYS, TERM('K'), MQ('K'), G('K')),
    'bvmchkslem3': '( ( %s /\\ N e. ( ZZ>= ` 2 ) ) -> ( %s - ( %s x. %s ) ) = ( sum_ n e. ( 1 ... ( N - 1 ) ) ( %s x. ( %s - %s ) ) - ( %s x. %s ) ) )'
                   % (HYS, SUMN('N'), CX('N'), CS('Y', 'N'), MQ('n'), G('n'), G('N'), CX('N'), CS('N', 'N')),
    'bvmchkslem2': '( ( %s /\\ ( N e. ( ZZ>= ` 2 ) /\\ N <_ Y ) ) -> ( abs ` ( sum_ n e. ( 1 ... ( N - 1 ) ) ( %s x. ( %s - %s ) ) - ( %s x. %s ) ) ) <_ ( %s x. ( %s - %s ) ) )'
                   % (HYS, MQ('n'), G('n'), G('N'), CX('N'), CS('N', 'N'), M113, R('1'), CX('N')),
    'bvmchks2': '( ( %s /\\ %s e. ( ZZ>= ` 2 ) ) -> ( abs ` %s ) <_ %s )' % (HYS, NY, SUMY, BOUND),
    'bvmchks1': '( ( %s /\\ %s = 1 ) -> ( abs ` %s ) <_ %s )' % (HYS, NY, SUMY, BOUND),
    'bvmchks': '( %s -> ( abs ` %s ) <_ %s )' % (HYS, SUMY, BOUND),
}

# $e hypotheses of the generic Abel lemmas (label suffix -> formula)
def _on(rng, body):
    return '( ( ph /\\ i e. %s ) -> %s )' % (rng, body)
FZN, FZN1 = '( 1 ... N )', '( 1 ... ( N + 1 ) )'
HYPS = {
    'bvabellem1': [('1', '( ph -> N e. NN )'),
                   ('2', '( ( ph /\\ n e. %s ) -> %s e. CC )' % (FZN, FA('n'))),
                   ('3', _on(FZN1, '%s e. CC' % FG('i')))],
    'bvabellem2': [('1', '( ph -> N e. NN )'),
                   ('2', _on(FZN, '%s e. CC' % FR('i'))),
                   ('3', _on(FZN1, '%s e. CC' % FF('i')))],
    'bvabellem3': [('1', '( ph -> N e. NN )'),
                   ('2', '( ph -> P e. CC )'),
                   ('3', '( ( ph /\\ n e. %s ) -> %s e. CC )' % (FZN, FA('n'))),
                   ('4', _on(FZN1, '%s e. CC' % FG('i'))),
                   ('5', _on(FZN, '%s e. CC' % FR('i'))),
                   ('6', _on(FZN, '%s e. CC' % FL('i'))),
                   ('7', _on(FZN1, '%s e. CC' % FF('i'))),
                   ('8', _on(FZN, '( %s - %s ) = ( %s x. %s )' % (FG('i'), FG('( i + 1 )'), FR('i'), FL('i')))),
                   ('9', _on(FZN, '%s = ( %s + ( %s x. %s ) )' % (FF('( i + 1 )'), FF('i'), FL('i'), ASA('i')))),
                   ('10', '( ph -> %s = 0 )' % FF('1'))],
    'bvabelin': [('1', '( ph -> N e. NN )'),
                 ('2', '( ph -> M e. RR )'),
                 ('3', '( ph -> P e. RR )'),
                 ('4', '( ( ph /\\ n e. %s ) -> %s e. RR )' % (FZN, FA('n'))),
                 ('5', _on(FZN1, '%s e. RR' % FG('i'))),
                 ('6', _on(FZN, '%s e. RR' % FR('i'))),
                 ('7', _on(FZN, '%s e. RR' % FL('i'))),
                 ('8', _on(FZN1, '%s e. RR' % FF('i'))),
                 ('9', _on(FZN, '( %s - %s ) = ( %s x. %s )' % (FG('i'), FG('( i + 1 )'), FR('i'), FL('i')))),
                 ('10', _on(FZN, '%s = ( %s + ( %s x. %s ) )' % (FF('( i + 1 )'), FF('i'), FL('i'), ASA('i')))),
                 ('11', '( ph -> %s = 0 )' % FF('1')),
                 ('12', _on(FZN1, '( abs ` %s ) <_ M' % FF('i'))),
                 ('13', _on('( 1 ..^ N )', '%s <_ %s' % (FR('( i + 1 )'), FR('i')))),
                 ('14', '( ph -> P <_ %s )' % FR('N'))],
}
ORDER = ['bvefge1p', 'bvexpl1', 'bvexpl2', 'bvchordlem2', 'bvchordlem3', 'bvchordlem4', 'bvchord', 'bvrlow',
         'bvrfirst', 'bvrlast', 'bvrmono', 'bvcshift', 'bvcp1', 'bvc1', 'bvabellem1', 'bvabellem2', 'bvabellem3',
         'bvabelin', 'bvmchkslem1', 'bvmchkslem3', 'bvmchkslem2', 'bvmchks2', 'bvmchks1', 'bvmchks']


def hyps_of(w, label):
    """write the $e hypothesis lines of LABEL into the worksheet; returns the step names"""
    from c0lib import hyp
    return [hyp(w, n, '%s.%s' % (label, n), f) for n, f in HYPS.get(label, [])]


def instl(w, ante0, ante1, A, k, T, step, body, mem):
    """from step: ( ( ante0 /\\ k e. A ) -> body ) and mem: ( ante1 -> T e. A ), where
    ante1 contains ante0 as a conjunct (cl.lift), derive ( ante1 -> body[T/k] );
    returns (step, new body).  `inst` needs ante0 = ante1; this lifts the
    generalisation first (T may contain the letters ante1 binds)."""
    ral = w.s([step], 'ralrimiva', '( %s -> A. %s e. %s %s )' % (ante0, k, A, body))
    rall = lift(w, ral, ante1)
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (k, T, k, T))
    st, new = w.wcongr(body, {k: T}, '%s = %s' % (k, T), {k: idk})
    return w.s([st, rall, mem], 'rspcdva', '( %s -> %s )' % (ante1, new)), new


def hyp2(w, ante1, phst, memst, hstep, concl):
    """from a $e-style step hstep: ( ( ph /\\ ps ) -> ch ), phst: ( ante1 -> ph ),
    memst: ( ante1 -> ps ): ( ante1 -> ch ) by syl2anc"""
    return w.s([phst, memst, hstep], 'syl2anc', '( %s -> %s )' % (ante1, concl))


def bind3(w, ante, s1, s2, s3, f1, f2, f3):
    return w.s([s1, s2, s3], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ante, f1, f2, f3))


def bind(w, ante, s1, s2, f1, f2):
    return w.s([s1, s2], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, f1, f2))


# ---- section 2 (mCheckQ): the frozen statements
IFQ = lambda n, q, x, s='S': 'if ( ( %s gcd %s ) = 1 , ( ( ( mmu ` %s ) x. ( %s ^c -u %s ) ) x. ( log ` ( %s / %s ) ) ) , 0 )' % (n, q, n, n, s, x, n)
MCQ = lambda q, x: '( %s ( mChkQ ` S ) %s )' % (q, x)
QSUM = lambda q, x: 'sum_ n e. ( 1 ... ( |_ ` %s ) ) %s' % (x, IFQ('n', q, x))
TERMX = lambda n, x: '( ( ( mmu ` %s ) x. ( %s ^c -u S ) ) x. ( log ` ( %s / %s ) ) )' % (n, n, x, n)
RAT = lambda q: '( %s / ( phi ` %s ) )' % (q, q)
BQ = lambda q, x: '( ( %s x. %s ) x. ( 1 + ( ( S - 1 ) x. ( log ` %s ) ) ) )' % (RAT(q), M113, x)
HPQ = '( P e. Prime /\\ Q e. NN /\\ ( P gcd Q ) = 1 )'
PQ = '( P x. Q )'
ALLX = lambda q: 'A. x e. RR ( 1 <_ x -> ( abs ` %s ) <_ %s )' % (MCQ(q, 'x'), BQ(q, 'x'))
PSI = lambda q, m: 'A. v e. RR ( ( 1 <_ v /\\ ( |_ ` v ) <_ %s ) -> ( abs ` %s ) <_ %s )' % (m, MCQ(q, 'v'), BQ(q, 'v'))
ALLXU = lambda q: 'A. u e. RR ( 1 <_ u -> ( abs ` %s ) <_ %s )' % (MCQ(q, 'u'), BQ(q, 'u'))
PHIQ = lambda q: '( ( mmu ` %s ) =/= 0 -> %s )' % (q, ALLX(q))

STATEMENTS2 = {
    'bvmchkqval': '( ( S e. RR /\\ Q e. NN /\\ X e. RR ) -> %s = %s )' % (MCQ('Q', 'X'), QSUM('Q', 'X')),
    'bvmchkqcl': '( ( S e. RR /\\ Q e. NN /\\ X e. RR ) -> %s e. RR )' % MCQ('Q', 'X'),
    'bvmchkq1': '( ( S e. RR /\\ X e. RR ) -> %s = sum_ n e. ( 1 ... ( |_ ` X ) ) %s )' % (MCQ('1', 'X'), TERMX('n', 'X')),
    'bvmchkq0': '( ( S e. RR /\\ Q e. NN /\\ ( X e. RR /\\ X < 1 ) ) -> %s = 0 )' % MCQ('Q', 'X'),
    'bvmuprm': '( P e. Prime -> ( mmu ` P ) = -u 1 )',
    'bvmchkqrec1': '( ( %s /\\ ( K e. NN /\\ ( S e. RR /\\ X e. RR+ ) ) ) -> %s = ( %s + if ( P || K , %s , 0 ) ) )' % (HPQ, IFQ('K', 'Q', 'X'), IFQ('K', PQ, 'X'), IFQ('K', 'Q', 'X')),
    'bvmchkqrec2': '( ( %s /\\ ( M e. NN /\\ ( S e. RR /\\ X e. RR+ ) ) ) -> %s = ( -u ( P ^c -u S ) x. %s ) )' % (HPQ, IFQ('( P x. M )', 'Q', 'X'), IFQ('M', PQ, '( X / P )')),
    'bvmchkqrec': '( ( ( S e. RR /\\ X e. RR ) /\\ %s ) -> %s = ( %s - ( ( P ^c -u S ) x. %s ) ) )' % (HPQ, MCQ('Q', 'X'), MCQ(PQ, 'X'), MCQ(PQ, '( X / P )')),
    'bvmchkqle1': '( Q e. NN -> 1 <_ %s )' % RAT('Q'),
    'bvmchkqrat': '( %s -> %s = ( ( P / ( P - 1 ) ) x. %s ) )' % (HPQ, RAT(PQ), RAT('Q')),
    'bvmchkqratlem': '( ( P e. RR /\\ 1 < P ) -> ( 1 + ( ( 1 / P ) x. ( P / ( P - 1 ) ) ) ) = ( P / ( P - 1 ) ) )',
    'bvmchkqbq0': '( ( %s /\\ ( Q e. NN /\\ ( X e. RR /\\ 1 <_ X ) ) ) -> 0 <_ %s )' % (HS, BQ('Q', 'X')),
    'bvmchkqbqle': '( ( %s /\\ ( Q e. NN /\\ ( ( X e. RR /\\ 1 <_ X ) /\\ ( Z e. RR /\\ 1 <_ Z /\\ Z <_ X ) ) ) ) -> %s <_ %s )' % (HS, BQ('Q', 'Z'), BQ('Q', 'X')),
    'bvmchkqindlem': '( ph -> ( abs ` %s ) <_ %s )' % (MCQ('R', 'X'), BQ('R', 'X')),
    'bvmchkqindn': '( ( ph /\\ N e. NN0 ) -> %s )' % PSI('R', 'N'),
    'bvmchkqind': '( ph -> %s )' % ALLXU('R'),
    'bvmchkq1b': '( %s -> %s )' % (HS, ALLX('1')),
    'bvmchkqstep': '( ( %s /\\ Q e. NN ) -> ( A. y e. ( 1 ... ( Q - 1 ) ) %s -> %s ) )' % (HS, PHIQ('y'), PHIQ('Q')),
    'bvmchkqall': '( ( %s /\\ Q e. NN ) -> %s )' % (HS, PHIQ('Q')),
    'bvmchkq': '( ( ( ( X e. RR /\\ 1 <_ X ) /\\ %s ) /\\ ( Q e. NN /\\ ( mmu ` Q ) =/= 0 ) ) -> ( abs ` %s ) <_ %s )' % (HS, MCQ('Q', 'X'), BQ('Q', 'X')),
}
HYPS2 = {
    'bvmchkqindlem': [('1', '( ph -> %s )' % HS), ('2', '( ph -> %s )' % HPQ), ('3', '( ph -> R = %s )' % PQ),
                      ('4', '( ph -> %s )' % ALLXU('Q')), ('5', '( ph -> N e. NN0 )'), ('6', '( ph -> %s )' % PSI('R', 'N')),
                      ('7', '( ph -> ( X e. RR /\\ 1 <_ X /\\ ( |_ ` X ) <_ ( N + 1 ) ) )')],
    'bvmchkqindn': [('1', '( ph -> %s )' % HS), ('2', '( ph -> %s )' % HPQ), ('3', '( ph -> R = %s )' % PQ), ('4', '( ph -> %s )' % ALLXU('Q'))],
    'bvmchkqind': [('1', '( ph -> %s )' % HS), ('2', '( ph -> %s )' % HPQ), ('3', '( ph -> R = %s )' % PQ), ('4', '( ph -> %s )' % ALLXU('Q'))],
}
ORDER2 = ['bvmchkqval', 'bvmchkqcl', 'bvmchkq1', 'bvmchkq0', 'bvmuprm', 'bvmchkqrec1', 'bvmchkqrec2', 'bvmchkqrec', 'bvmchkqle1',
          'bvmchkqrat', 'bvmchkqratlem', 'bvmchkqbq0', 'bvmchkqbqle', 'bvmchkqindlem', 'bvmchkqindn', 'bvmchkqind', 'bvmchkq1b', 'bvmchkqstep',
          'bvmchkqall', 'bvmchkq']
STATEMENTS.update(STATEMENTS2); HYPS.update(HYPS2)


# ---- section 3 (the phiSig block, sum_squarefree_prod_le, uSeq, W_bound)
PRF = lambda d: '{ q e. Prime | q || %s }' % d
DV = lambda n: '{ x e. NN | x || %s }' % n
SQDV = lambda n: '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || %s ) }' % n
PR = lambda m: '( ( 1 ... %s ) i^i Prime )' % m
RAD = lambda m: 'prod_ r e. %s r' % PR(m)          # the radical, bound letter r (sqfdvdsum has $d N p)
RADP = lambda m: 'prod_ p e. %s p' % PR(m)         # set.mm's form (sqfprod, sqfdvdprod)
PHS = lambda s, q: 'prod_ p e. %s ( ( p ^c %s ) - 1 )' % (PRF(q), s)
U = lambda n: '( ( ( 2 x. %s ) - 1 ) / ( %s x. ( ( %s - 1 ) ^ 2 ) ) )' % (n, n, n)
GS = lambda p: '( ( ( 2 x. %s ) - 1 ) / ( ( %s - 1 ) ^ 2 ) )' % (p, p)
HS0 = '( S e. RR /\\ 0 <_ S )'
SQF = lambda q: '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (q, q)
IFF = lambda a: 'if ( ( mmu ` %s ) =/= 0 , ( prod_ p e. %s %s / %s ) , 0 )' % (a, PRF(a), GS('p'), a)
IFG = lambda b: 'if ( ( mmu ` %s ) =/= 0 , ( 1 / %s ) , 0 )' % (b, b)
WTERM = lambda d: 'if ( ( mmu ` %s ) =/= 0 , ( ( %s x. ( %s ^c ( -u 2 x. S ) ) ) x. ( ( %s / ( phi ` %s ) ) ^ 2 ) ) , 0 )' % (d, PHS('S', d), d, d, d)
LOGM = '( 1 + ( log ` M ) )'

STATEMENTS3 = {
    'bvfprodcxp': '( ph -> prod_ k e. A ( ( F ` k ) ^c S ) = ( prod_ k e. A ( F ` k ) ^c S ) )',
    'bvprodle1': '( ph -> prod_ k e. A C <_ prod_ k e. B C )',
    'bvphisg0': '( ( %s /\\ Q e. NN ) -> 0 <_ %s )' % (HS0, PHS('S', 'Q')),
    'bvsqdv': '( %s -> %s = %s )' % (SQF('N'), SQDV('N'), DV('N')),
    'bvphisgle': '( ( %s /\\ %s ) -> %s <_ ( Q ^c S ) )' % (HS0, SQF('Q'), PHS('S', 'Q')),
    'bvphisgsum': '( ( S e. RR /\\ %s ) -> sum_ d e. %s %s = ( N ^c S ) )' % (SQF('N'), DV('N'), PHS('S', 'd')),
    'bvsqfsumlem1': '( ( M e. NN /\\ ( D e. ( 1 ... M ) /\\ ( mmu ` D ) =/= 0 ) ) -> D e. %s )' % SQDV(RAD('M')),
    'bvsqfsumlem2': '( ( M e. NN /\\ D e. %s ) -> %s C_ ( 2 ... M ) )' % (SQDV(RAD('M')), PRF('D')),
    'bvsqfsum': '( ph -> sum_ a e. ( 1 ... M ) if ( ( mmu ` a ) =/= 0 , prod_ p e. %s ( W ` p ) , 0 ) <_ prod_ n e. ( 2 ... M ) ( 1 + ( W ` n ) ) )' % PRF('a'),
    'bvuseq0': '( N e. ( ZZ>= ` 2 ) -> 0 <_ %s )' % U('N'),
    'bvuseqrat': '( N e. ( ZZ>= ` 4 ) -> ( ( 1 + %s ) x. ( N x. ( N - 3 ) ) ) <_ ( ( N - 1 ) x. ( N - 2 ) ) )' % U('N'),
    'bvuprodind': '( M e. ( ZZ>= ` 6 ) -> ( ( 3 x. M ) x. prod_ n e. ( 6 ... M ) ( 1 + %s ) ) <_ ( 5 x. ( M - 2 ) ) )' % U('n'),
    'bvuprod5': 'prod_ n e. ( 2 ... 5 ) ( 1 + %s ) <_ ( ; 2 4 / 5 )' % U('n'),
    'bvuprodtail': '( M e. ( ZZ>= ` 6 ) -> prod_ n e. ( 6 ... M ) ( 1 + %s ) <_ ( 5 / 3 ) )' % U('n'),
    'bvuprod': '( M e. NN -> prod_ n e. ( 2 ... M ) ( 1 + %s ) <_ 8 )' % U('n'),
    'bvsqtot': '( %s -> ( ( N / ( phi ` N ) ) ^ 2 ) = sum_ d e. %s prod_ p e. %s %s )' % (SQF('N'), DV('N'), PRF('d'), GS('p')),
    'bvgsu': '( %s -> ( prod_ p e. %s %s / A ) = prod_ p e. %s %s )' % (SQF('A'), PRF('A'), GS('p'), PRF('A'), U('p')),
    'bvwbndlem1': '( ( %s /\\ %s ) -> ( %s x. ( D ^c ( -u 2 x. S ) ) ) <_ ( 1 / D ) )' % (HS, SQF('D'), PHS('S', 'D')),
    'bvwbndlem2': '( %s -> ( ( 1 / N ) x. ( ( N / ( phi ` N ) ) ^ 2 ) ) = sum_ d e. %s ( %s x. %s ) )' % (SQF('N'), DV('N'), IFF('d'), IFG('( N / d )')),
    'bvwbndlem3': '( M e. NN -> sum_ n e. ( 1 ... M ) sum_ d e. %s ( %s x. %s ) <_ ( sum_ d e. ( 1 ... M ) %s x. %s ) )' % (DV('n'), IFF('d'), IFG('( n / d )'), IFF('d'), LOGM),
    'bvwbndlem4': '( M e. NN -> sum_ d e. ( 1 ... M ) %s <_ 8 )' % IFF('d'),
    'bvwbnd': '( ( %s /\\ M e. NN ) -> sum_ n e. ( 1 ... M ) %s <_ ( 8 x. %s ) )' % (HS, WTERM('n'), LOGM),
}
HYPS3 = {
    'bvfprodcxp': [('1', '( ph -> A e. Fin )'), ('2', '( ph -> S e. RR )'), ('3', '( ( ph /\\ k e. A ) -> ( F ` k ) e. RR+ )')],
    'bvprodle1': [('1', '( ph -> B e. Fin )'), ('2', '( ph -> A C_ B )'), ('3', '( ( ph /\\ k e. B ) -> C e. RR )'), ('4', '( ( ph /\\ k e. B ) -> 1 <_ C )')],
    'bvsqfsum': [('1', '( ph -> M e. NN )'), ('2', '( ( ph /\\ n e. ( 2 ... M ) ) -> ( W ` n ) e. RR )'), ('3', '( ( ph /\\ n e. ( 2 ... M ) ) -> 0 <_ ( W ` n ) )')],
}
ORDER3 = ['bvfprodcxp', 'bvprodle1', 'bvphisg0', 'bvsqdv', 'bvphisgle', 'bvphisgsum', 'bvsqfsumlem1', 'bvsqfsumlem2', 'bvsqfsum',
          'bvuseq0', 'bvuseqrat', 'bvuprodind', 'bvuprod5', 'bvuprodtail', 'bvuprod', 'bvsqtot', 'bvgsu',
          'bvwbndlem1', 'bvwbndlem2', 'bvwbndlem3', 'bvwbndlem4', 'bvwbnd']
STATEMENTS.update(STATEMENTS3); HYPS.update(HYPS3)


# ---- closed numeral evaluation (integer expressions with + - x. ^ 2)
def numev(w, expr):
    """(closed step proving ( expr = lit ), value) for an integer numeral expression
    built from + - x. and ^ 2; (None, value) when expr is already a numeral"""
    import num
    from cl import split_top
    expr = ' '.join(expr.split())
    v = num.lit_value(expr) if num.is_lit(expr) else None
    if v is not None:
        assert v.denominator == 1 and v >= 0, expr
        return None, int(v)
    toks = expr.split()
    A, op, B = split_top(toks[1:-1])
    sa, a = numev(w, A)
    sb, b = numev(w, B)
    na, nb = num.nat_text(a), num.nat_text(b)
    if op == '^':
        assert b == 2, expr
        s1 = num.closed(w, [num.cc_nat(w, a)], 'sqvali', '( %s ^ 2 ) = ( %s x. %s )' % (na, na, na))
        s2 = num.mul_nat(w, a, a)
        fact = num.closed(w, [s1, s2], 'eqtri', '( %s ^ 2 ) = %s' % (na, num.nat_text(a * a)))
        val = a * a
    elif op == '+':
        fact = num.add_nat(w, a, b); val = a + b
    elif op == '-':
        fact = num.sub_nat(w, a, b); val = a - b
    elif op == 'x.':
        fact = num.mul_nat(w, a, b); val = a * b
    else:
        raise ValueError(expr)
    mid = '( %s %s %s )' % (na, op, nb)
    if sa is None and sb is None:
        return fact, val
    if sa is not None and sb is not None:
        cg = num.closed(w, [sa, sb], 'oveq12i', '%s = %s' % (expr, mid))
    elif sa is not None:
        cg = num.closed(w, [sa], 'oveq1i', '%s = %s' % (expr, mid))
    else:
        cg = num.closed(w, [sb], 'oveq2i', '%s = %s' % (expr, mid))
    return num.closed(w, [cg, fact], 'eqtri', '%s = %s' % (expr, num.nat_text(val))), val


def fracev(w, expr):
    """closed step ( ( N / D ) = ( n / d ) ) for numeral expressions N, D whose values are coprime
    (the canonical fraction literal); returns (step, text)"""
    import num
    from cl import split_top
    toks = expr.split()
    Nn, op, Dd = split_top(toks[1:-1])
    assert op == '/'
    sn, n = numev(w, Nn); sd, d = numev(w, Dd)
    from math import gcd
    assert gcd(n, d) == 1, expr
    txt = '( %s / %s )' % (num.nat_text(n), num.nat_text(d))
    if sn is not None and sd is not None:
        return num.closed(w, [sn, sd], 'oveq12i', '%s = %s' % (expr, txt)), txt
    if sn is not None:
        return num.closed(w, [sn], 'oveq1i', '%s = %s' % (expr, txt)), txt
    return num.closed(w, [sd], 'oveq2i', '%s = %s' % (expr, txt)), txt


# ---- section 4 (the diagonalisation): the frozen statements
ZS = lambda s='S': 'sum_ n e. NN ( n ^c -u %s )' % s                    # zeta ( S )
ALs = lambda j, N='N': 'sum_ d e. ( 1 ... %s ) if ( d || %s , ( L ` d ) , 0 )' % (N, j)
TDE = lambda j, d='d', e='e': '( ( ( L ` %s ) x. ( L ` %s ) ) x. if ( ( %s lcm %s ) || %s , ( %s ^c -u S ) , 0 ) )' % (d, e, d, e, j, j)
LCMS = lambda d='d', e='e': '( ( ( L ` %s ) x. ( L ` %s ) ) x. ( ( %s lcm %s ) ^c -u S ) )' % (d, e, d, e)
DSUM = lambda N='N': 'sum_ d e. ( 1 ... %s ) sum_ e e. ( 1 ... %s ) %s' % (N, N, LCMS())
SG = lambda m, N='N': 'sum_ d e. ( 1 ... %s ) if ( %s || d , ( ( L ` d ) x. ( d ^c -u S ) ) , 0 )' % (N, m)
HS1 = '( S e. RR /\\ 1 < S )'
STATEMENTS4 = {
    'bvmultcvg': '( ( %s /\\ M e. NN ) -> seq 1 ( + , ( t e. NN |-> if ( M || t , ( t ^c -u S ) , 0 ) ) ) e. dom ~~> )' % HS1,
    'bvswap': '( ph -> seq 1 ( + , ( t e. NN |-> sum_ k e. A D ) ) ~~> sum_ k e. A sum_ j e. NN C )',
    'bvtsumpt': '( ph -> ( ( J ^c -u S ) x. ( %s ^ 2 ) ) = sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s )' % (ALs('J'), TDE('J')),
    'bvtsumlem': '( ph -> seq 1 ( + , ( t e. NN |-> %s ) ) ~~> ( %s x. %s ) )' % (TDE('t', 'D', 'E'), LCMS('D', 'E'), ZS()),
    'bvtsum': '( ph -> seq 1 ( + , ( t e. NN |-> ( ( t ^c -u S ) x. ( %s ^ 2 ) ) ) ) ~~> ( %s x. %s ) )' % (ALs('t'), ZS(), DSUM()),
}
HYPS4 = {
    'bvswap': [('1', '( ph -> A e. Fin )'), ('2', '( ( ph /\\ ( k e. A /\\ j e. NN ) ) -> C e. CC )'),
               ('3', '( ( ph /\\ k e. A ) -> seq 1 ( + , ( t e. NN |-> D ) ) e. dom ~~> )'), ('4', '( j = t -> C = D )')],
    'bvtsumpt': [('1', '( ph -> ( S e. RR /\\ J e. NN ) )'), ('2', '( ph -> N e. NN )'),
                 ('3', '( ( ph /\\ d e. ( 1 ... N ) ) -> ( L ` d ) e. RR )')],
    'bvtsumlem': [('1', '( ph -> %s )' % HS1), ('2', '( ph -> ( D e. NN /\\ E e. NN ) )'),
                  ('3', '( ph -> ( ( L ` D ) e. RR /\\ ( L ` E ) e. RR ) )')],
    'bvtsum': [('1', '( ph -> %s )' % HS1), ('2', '( ph -> N e. NN )'),
               ('3', '( ( ph /\\ d e. ( 1 ... N ) ) -> ( L ` d ) e. RR )')],
}
ORDER4 = ['bvmultcvg', 'bvswap', 'bvtsumpt', 'bvtsumlem', 'bvtsum']
STATEMENTS.update(STATEMENTS4); HYPS.update(HYPS4)


def gramcheck(labels):
    """grammar-check frozen statements: a worksheet per label with the $e lines and a bare qed"""
    import mm as _MM, re as _re
    from c0lib import hyp
    out = {}
    for lab in labels:
        w = W('zbv2g' + lab.replace('.', ''), 'grammar check of %s' % lab)
        hs = [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        path = w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out

# ---- section 4 part B: the Selberg diagonalisation for a generic weight L
XDm = lambda m, D: 'if ( %s || %s , ( ( L ` %s ) x. ( %s ^c -u S ) ) , 0 )' % (m, D, D, D)
STATEMENTS5 = {
    'bvlcmcxp': '( ( ( D e. NN /\\ E e. NN ) /\\ S e. RR ) -> ( ( D lcm E ) ^c -u S ) = ( ( ( D gcd E ) ^c S ) x. ( ( D ^c -u S ) x. ( E ^c -u S ) ) ) )',
    'bvdiagsum': '( ( ( S e. RR /\\ N e. NN ) /\\ ( ( D e. ( 1 ... N ) /\\ E e. ( 1 ... N ) ) /\\ ( ( mmu ` D ) =/= 0 /\\ ( mmu ` E ) =/= 0 ) ) ) -> '
                 'sum_ m e. ( 1 ... N ) if ( ( m || D /\\ m || E ) , %s , 0 ) = ( ( D gcd E ) ^c S ) )' % PHS('S', 'm'),
    'bvdiagpt': '( ph -> %s = sum_ m e. ( 1 ... N ) ( %s x. ( %s x. %s ) ) )' % (LCMS('D', 'E'), PHS('S', 'm'), XDm('m', 'D'), XDm('m', 'E')),
    'bvdiag': '( ph -> %s = sum_ m e. ( 1 ... N ) ( %s x. ( %s ^ 2 ) ) )' % (DSUM(), PHS('S', 'm'), SG('m')),
}
HYPS5 = {
    'bvdiagpt': [('1', '( ph -> ( S e. RR /\\ N e. NN ) )'), ('2', '( ph -> ( D e. ( 1 ... N ) /\\ E e. ( 1 ... N ) ) )'),
                 ('3', '( ph -> ( ( L ` D ) e. RR /\\ ( L ` E ) e. RR ) )'),
                 ('4', '( ph -> ( ( ( mmu ` D ) = 0 -> ( L ` D ) = 0 ) /\\ ( ( mmu ` E ) = 0 -> ( L ` E ) = 0 ) ) )')],
    'bvdiag': [('1', '( ph -> S e. RR )'), ('2', '( ph -> N e. NN )'), ('3', '( ( ph /\\ d e. ( 1 ... N ) ) -> ( L ` d ) e. RR )'),
               ('4', '( ( ph /\\ d e. ( 1 ... N ) ) -> ( ( mmu ` d ) = 0 -> ( L ` d ) = 0 ) )')],
}
ORDER5 = ['bvlcmcxp', 'bvdiagsum', 'bvdiagpt', 'bvdiag']
STATEMENTS.update(STATEMENTS5); HYPS.update(HYPS5)

# ---- section 4 part C: the Barban-Vehov weight, S_delta, the assembled bounds, Rankin, the endgame
PL = lambda x: 'if ( 1 <_ %s , ( log ` %s ) , 0 )' % (x, x)          # Real.posLog x for x > 0
LGAB = '( log ` ( B / A ) )'
BVL = lambda y: '( ( ( mmu ` %s ) x. ( %s - %s ) ) / %s )' % (y, PL('( B / %s )' % y), PL('( A / %s )' % y), LGAB)
HL = 'L = ( z e. NN |-> %s )' % BVL('z')                                 # bvLam A B, A = z1, B = z2
HAB = '( ( A e. RR /\\ 1 <_ A ) /\\ ( B e. RR /\\ A < B ) )'
NB = '( |_ ` B )'
SGB = lambda m: SG(m, NB)                                                # Ssum A B S m
IFP = lambda n, q, x: 'if ( ( %s gcd %s ) = 1 , ( ( ( mmu ` %s ) x. ( %s ^c -u S ) ) x. %s ) , 0 )' % (n, q, n, n, PL('( %s / %s )' % (x, n)))
KB = '( ( ( ; 2 2 / 3 ) x. ( 1 + ( ( S - 1 ) x. ( log ` B ) ) ) ) / %s )' % LGAB
TSQ = lambda s, N: 'sum_ n e. NN ( ( n ^c -u %s ) x. ( %s ^ 2 ) )' % (s, ALs('n', N))
TSQC = lambda s, N: 'seq 1 ( + , ( n e. NN |-> ( ( n ^c -u %s ) x. ( %s ^ 2 ) ) ) ) e. dom ~~>' % (s, ALs('n', N))
BVA = lambda n: 'sum_ d e. { x e. NN | x || %s } ( L ` d )' % n
SR = '( 1 + ( 1 / ( log ` Y ) ) )'
ELLD = '( ( 1 / ; ; 1 0 0 ) x. ( log ` D ) )'
C5 = '; ; ; ; ; 5 0 0 0 0 0'
HZ1 = 'A = ( D ^c ( ; 3 1 / ; 5 0 ) )'
HZ2 = 'B = ( D ^c ( ; 6 3 / ; ; 1 0 0 ) )'
HD = '( ( D e. RR /\\ 1 < D ) /\\ ( ; ; 1 0 0 <_ A /\\ ( Y e. RR /\\ A <_ Y ) ) )'
STATEMENTS6 = {
    'bvmunc': '( ( ( M e. NN /\\ K e. NN ) /\\ -. ( K gcd M ) = 1 ) -> ( mmu ` ( M x. K ) ) = 0 )',
    'bvsspl': '( ( ( S e. RR /\\ Q e. NN ) /\\ ( X e. RR+ /\\ ( M e. NN0 /\\ ( |_ ` X ) <_ M ) ) ) -> sum_ n e. ( 1 ... M ) %s = %s )' % (IFP('n', 'Q', 'X'), MCQ('Q', 'X')),
    'bvlamterm': '( ( ( %s /\\ S e. RR ) /\\ ( M e. NN /\\ K e. NN ) ) -> ( ( L ` ( M x. K ) ) x. ( ( M x. K ) ^c -u S ) ) = ( ( ( ( mmu ` M ) x. ( M ^c -u S ) ) / %s ) x. ( %s - %s ) ) )'
                 % (HAB, LGAB, IFP('K', 'M', '( B / M )'), IFP('K', 'M', '( A / M )')),
    'bvssumq': '( ( ( %s /\\ S e. RR ) /\\ M e. NN ) -> %s = ( ( ( ( mmu ` M ) x. ( M ^c -u S ) ) / %s ) x. ( %s - %s ) ) )'
               % (HAB, SGB('M'), LGAB, MCQ('M', '( B / M )'), MCQ('M', '( A / M )')),
    'bvssumle': '( ( ( %s /\\ ( S e. RR /\\ 1 <_ S ) ) /\\ ( M e. ( 1 ... %s ) /\\ ( mmu ` M ) =/= 0 ) ) -> ( abs ` %s ) <_ ( ( ( M ^c -u S ) x. ( M / ( phi ` M ) ) ) x. %s ) )'
                % (HAB, NB, SGB('M'), KB),
    'bvdiagle': '( ph -> ( %s /\\ %s <_ ( %s x. ( ( K ^ 2 ) x. ( 8 x. ( 1 + ( log ` N ) ) ) ) ) ) )' % (TSQC('S', 'N'), TSQ('S', 'N'), ZS()),
    'bvaicc': '( ( %s /\\ K e. NN ) -> %s = %s )' % (HAB, BVA('K'), ALs('K', NB)),
    'bvtsumle': '( ( %s /\\ ( S e. RR /\\ 1 < S ) ) -> ( %s /\\ %s <_ ( %s x. ( ( %s ^ 2 ) x. ( 8 x. ( 1 + ( log ` %s ) ) ) ) ) ) )'
                % (HAB, TSQC('S', NB), TSQ('S', NB), ZS(), KB, NB),
    'bvrankin': '( ph -> sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( C ^ 2 ) / n ) <_ ( ( exp ` 1 ) x. sum_ n e. NN ( ( n ^c -u %s ) x. ( C ^ 2 ) ) ) )' % SR,
    'bvrankina': '( ph -> sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( n ^c ( 1 - ( 2 x. T ) ) ) x. ( C ^ 2 ) ) <_ ( ( Y ^c ( 2 - ( 2 x. T ) ) ) x. sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( C ^ 2 ) / n ) ) )',
    'bvharm': '( %s -> sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( %s ^ 2 ) / n ) <_ ( ( %s x. ( log ` Y ) ) / %s ) )' % (HD, BVA('n'), C5, ELLD),
    'bvl2star': '( ( %s /\\ ( T e. RR /\\ ( ( 1 / 2 ) <_ T /\\ T <_ 1 ) ) ) -> sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( n ^c ( 1 - ( 2 x. T ) ) ) x. ( %s ^ 2 ) ) <_ ( ( ( %s x. ( Y ^c ( 2 - ( 2 x. T ) ) ) ) x. ( log ` Y ) ) / %s ) )'
                % (HD, BVA('n'), C5, ELLD),
}
HYPS6 = {
    'bvlamterm': [('1', HL)], 'bvssumq': [('1', HL)], 'bvssumle': [('1', HL)], 'bvaicc': [('1', HL)], 'bvtsumle': [('1', HL)],
    'bvdiagle': [('1', '( ph -> %s )' % HS1), ('2', '( ph -> N e. NN )'), ('3', '( ( ph /\\ d e. ( 1 ... N ) ) -> ( L ` d ) e. RR )'),
                 ('4', '( ( ph /\\ d e. ( 1 ... N ) ) -> ( ( mmu ` d ) = 0 -> ( L ` d ) = 0 ) )'), ('5', '( ph -> K e. RR )'),
                 ('6', '( ( ph /\\ ( m e. ( 1 ... N ) /\\ ( mmu ` m ) =/= 0 ) ) -> ( abs ` %s ) <_ ( ( ( m ^c -u S ) x. ( m / ( phi ` m ) ) ) x. K ) )' % SG('m'))],
    'bvrankin': [('1', '( ph -> ( Y e. RR /\\ 1 < Y ) )'), ('2', '( ( ph /\\ n e. NN ) -> C e. RR )'),
                 ('3', '( ph -> seq 1 ( + , ( t e. NN |-> ( ( t ^c -u %s ) x. ( D ^ 2 ) ) ) ) e. dom ~~> )' % SR), ('4', '( n = t -> C = D )')],
    'bvrankina': [('1', '( ph -> ( Y e. RR /\\ 1 <_ Y ) )'), ('2', '( ph -> ( T e. RR /\\ T <_ 1 ) )'),
                  ('3', '( ( ph /\\ n e. ( 1 ... ( |_ ` Y ) ) ) -> C e. RR )')],
    'bvharm': [('1', HZ1), ('2', HZ2), ('3', HL)],
    'bvl2star': [('1', HZ1), ('2', HZ2), ('3', HL)],
}
ORDER6 = ['bvmunc', 'bvsspl', 'bvlamterm', 'bvssumq', 'bvssumle', 'bvdiagle', 'bvaicc', 'bvtsumle', 'bvrankin', 'bvrankina', 'bvharm', 'bvl2star']
STATEMENTS.update(STATEMENTS6); HYPS.update(HYPS6)

# ---- section 4 part C: the endgame numerals (internal to bvharm)
STATEMENTS7 = {
    'bvebnd': '( exp ` 1 ) <_ ( ; 2 9 / ; 1 0 )',
    'bvlog100': '4 <_ ( log ` ; ; 1 0 0 )',
    'bvharmnum': '( ( ( ( E e. RR /\\ 0 <_ E /\\ E <_ ( ; 2 9 / ; 1 0 ) ) /\\ ( Z e. RR /\\ 0 <_ Z /\\ Z <_ ( 1 + V ) ) ) /\\ '
                 '( ( K e. RR /\\ 0 <_ K /\\ ( K x. W ) <_ ( ; ; ; 1 3 7 5 / ; 9 3 ) ) /\\ ( G e. RR /\\ 0 <_ G /\\ G <_ ( ; 6 3 x. W ) ) /\\ '
                 '( ( W e. RR /\\ V e. RR ) /\\ ( 4 <_ ( ; 6 2 x. W ) /\\ ( ; 6 2 x. W ) <_ V ) ) ) ) -> '
                 '( E x. ( Z x. ( ( K ^ 2 ) x. ( 8 x. ( 1 + G ) ) ) ) ) <_ ( ( %s x. V ) / W ) )' % C5,
}
ORDER7 = ['bvebnd', 'bvlog100', 'bvharmnum']
STATEMENTS.update(STATEMENTS7)


def le_lit2(w, A, B, strict=False):
    """num.le_lit, with its integer-left / fraction-right branch repaired (num.le_lit
    closes that branch by mpbir where the biconditional needs mpbi; see the tooling
    note in ZBV2-HANDOFF.md).  Closed step A <_ B (A < B with strict)."""
    import num
    va, vb = num.lit_value(A), num.lit_value(B)
    assert va is not None and vb is not None and 0 <= va <= vb and (va < vb or not strict), (A, B)
    if va.denominator == 1 and vb.denominator == 1:
        return num.le_nat(w, va, vb, strict)
    rel = '<' if strict else '<_'
    f = '%s %s %s' % (A, rel, B)
    if va.denominator != 1:
        p, q = va.numerator, va.denominator; tp, tq = num.nat_text(p), num.nat_text(q)
        i = w.inst('ltdivmul' if strict else 'ledivmul')
        bi = num.closed(w, [num.re_nat(w, p), num.real(w, B), num._pos(w, q), i], 'mp3an',
                        '( %s <-> %s %s ( %s x. %s ) )' % (f, tp, rel, tq, B))
        core = le_lit2(w, tp, num.lit_text(q * vb), strict)
        s_ = num.closed(w, [core, num.mul_lits(w, tq, B)], 'breqtrri', '%s %s ( %s x. %s )' % (tp, rel, tq, B))
        return num.closed(w, [s_, bi], 'mpbir', f)
    n = va.numerator; r_, s_ = vb.numerator, vb.denominator
    tn, tr, ts = num.nat_text(n), num.nat_text(r_), num.nat_text(s_)
    i = w.inst('ltmuldiv' if strict else 'lemuldiv')
    bi = num.closed(w, [num.re_nat(w, n), num.re_nat(w, r_), num._pos(w, s_), i], 'mp3an',
                    '( ( %s x. %s ) %s %s <-> %s )' % (tn, ts, rel, tr, f))
    core = num.le_nat(w, n * s_, r_, strict)
    s2 = num.closed(w, [num.mul_nat(w, n, s_), core], 'eqbrtri', '( %s x. %s ) %s %s' % (tn, ts, rel, tr))
    return num.closed(w, [s2, bi], 'mpbi', f)
