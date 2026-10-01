"""C7, Perron block 2: the coordinate rectangle identities and the far abscissae."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure
from lin import linarith, lineq

PQSR = '( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ R e. RR ) )'
CA = CPT('P', 'S'); CB = CPT('Q', 'R')


def corners(w, A0, urp, pqsr):
    """steps: pr qr sr rr, ac bc (the two corners in CC), pk0v ( PK0 e. _V ),
    rco ( the rectint in coordinate form )"""
    pr = w.s([w.s([pqsr, w.inst('simpl')], 'syl', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> P e. RR )' % A0)
    qr = w.s([w.s([pqsr, w.inst('simpl')], 'syl', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> Q e. RR )' % A0)
    sr = w.s([w.s([pqsr, w.inst('simpr')], 'syl', '( %s -> ( S e. RR /\\ R e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
    rr = w.s([w.s([pqsr, w.inst('simpr')], 'syl', '( %s -> ( S e. RR /\\ R e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> R e. RR )' % A0)
    ic = a1(w, A0, 'ax-icn', '_i e. CC')
    def cpt(x, y, xr, yr):
        return w.s([w.s([xr], 'recnd', '( %s -> %s e. CC )' % (A0, x)),
                    w.s([ic, w.s([yr], 'recnd', '( %s -> %s e. CC )' % (A0, y))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, y))],
                   'addcld', '( %s -> %s e. CC )' % (A0, CPT(x, y)))
    ac = cpt('P', 'S', pr, sr); bc = cpt('Q', 'R', qr, rr)
    dex = w.s([a1(w, A0, 'cnex', 'CC e. _V'), w.inst('difexg')], 'syl', '( %s -> %s e. _V )' % (A0, DOM))
    pk0v = w.s([dex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, PK0))
    rco = w.s([pk0v, w.s([pr, qr], 'jca', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A0), w.s([sr, rr], 'jca', '( %s -> ( S e. RR /\\ R e. RR ) )' % A0),
               w.inst('rectintco')], 'syl3anc', '( %s -> ( %s rectint <. %s , %s >. ) = %s )' % (A0, PK0, CA, CB, FOUR(PK0, 'P', 'Q', 'S', 'R')))
    d = dict(pr=pr, qr=qr, sr=sr, rr=rr, ac=ac, bc=bc, rco=rco)
    d['rea'] = w.s([pr, sr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = P )' % (A0, CA))
    d['ima'] = w.s([pr, sr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = S )' % (A0, CA))
    d['reb'] = w.s([qr, rr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = Q )' % (A0, CB))
    d['imb'] = w.s([qr, rr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = R )' % (A0, CB))
    return d


# ---------------------------------------------------------------- pkrecidc
INT = '( ( P < 0 /\\ 0 < Q ) /\\ ( S < 0 /\\ 0 < R ) )'
A0 = '( U e. RR+ /\\ %s /\\ %s )' % (PQSR, INT)
w = W('pkrecidc', 'Perron\'s contour with the pole inside, in coordinates: the four edges of '
      'the rectangle with corners ` P + _i S ` and ` Q + _i R ` around the origin sum to '
      '` 2 _i _pi ` ( ~ pkrecid , ~ rectintco ).')
urp = w.s([], 'simp1', '( %s -> U e. RR+ )' % A0)
pqsr = w.s([], 'simp2', '( %s -> %s )' % (A0, PQSR))
ints = w.s([], 'simp3', '( %s -> %s )' % (A0, INT))
d = corners(w, A0, urp, pqsr)
i1 = w.s([ints, w.inst('simpll')], 'syl', '( %s -> P < 0 )' % A0)
i2 = w.s([ints, w.inst('simplr')], 'syl', '( %s -> 0 < Q )' % A0)
i3 = w.s([ints, w.inst('simprl')], 'syl', '( %s -> S < 0 )' % A0)
i4 = w.s([ints, w.inst('simprr')], 'syl', '( %s -> 0 < R )' % A0)
j1 = w.s([d['rea'], i1], 'eqbrtrd', '( %s -> ( Re ` %s ) < 0 )' % (A0, CA))
j2 = w.s([i2, w.s([d['reb']], 'eqcomd', '( %s -> Q = ( Re ` %s ) )' % (A0, CB))], 'breqtrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, CB))
j3 = w.s([d['ima'], i3], 'eqbrtrd', '( %s -> ( Im ` %s ) < 0 )' % (A0, CA))
j4 = w.s([i4, w.s([d['imb']], 'eqcomd', '( %s -> R = ( Im ` %s ) )' % (A0, CB))], 'breqtrd', '( %s -> 0 < ( Im ` %s ) )' % (A0, CB))
hyp = w.s([w.s([j1, j2], 'jca', '( %s -> ( ( Re ` %s ) < 0 /\\ 0 < ( Re ` %s ) ) )' % (A0, CA, CB)),
           w.s([j3, j4], 'jca', '( %s -> ( ( Im ` %s ) < 0 /\\ 0 < ( Im ` %s ) ) )' % (A0, CA, CB))], 'jca',
          '( %s -> ( ( ( Re ` %s ) < 0 /\\ 0 < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < 0 /\\ 0 < ( Im ` %s ) ) ) )' % (A0, CA, CB, CA, CB))
rid = w.s([urp, w.s([d['ac'], d['bc']], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CA, CB)), hyp, w.inst('pkrecid')], 'syl3anc',
          '( %s -> ( %s rectint <. %s , %s >. ) = %s )' % (A0, PK0, CA, CB, TPI))
w.qed([d['rco'], rid], 'eqtr3d', '( %s -> %s = %s )' % (A0, FOUR(PK0, 'P', 'Q', 'S', 'R'), TPI))
run7(w)

# ---------------------------------------------------------------- pkrecid0c
GEO = '( ( P <_ Q /\\ S <_ R ) /\\ 0 < P )'
A0 = '( U e. RR+ /\\ %s /\\ %s )' % (PQSR, GEO)
w = W('pkrecid0c', 'The pole-free Perron rectangle in coordinates: the four edges of a '
      'rectangle in the open right half-plane sum to zero ( ~ pkrecid0 , ~ rectintco ).')
urp = w.s([], 'simp1', '( %s -> U e. RR+ )' % A0)
pqsr = w.s([], 'simp2', '( %s -> %s )' % (A0, PQSR))
geo = w.s([], 'simp3', '( %s -> %s )' % (A0, GEO))
d = corners(w, A0, urp, pqsr)
g1 = w.s([geo, w.inst('simpll')], 'syl', '( %s -> P <_ Q )' % A0)
g2 = w.s([geo, w.inst('simplr')], 'syl', '( %s -> S <_ R )' % A0)
g3 = w.s([geo, w.inst('simpr')], 'syl', '( %s -> 0 < P )' % A0)
k1 = w.s([d['rea'], w.s([g1, w.s([d['reb']], 'eqcomd', '( %s -> Q = ( Re ` %s ) )' % (A0, CB))], 'breqtrd', '( %s -> P <_ ( Re ` %s ) )' % (A0, CB))],
         'eqbrtrd', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, CA, CB))
k2 = w.s([d['ima'], w.s([g2, w.s([d['imb']], 'eqcomd', '( %s -> R = ( Im ` %s ) )' % (A0, CB))], 'breqtrd', '( %s -> S <_ ( Im ` %s ) )' % (A0, CB))],
         'eqbrtrd', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, CA, CB))
k3 = w.s([g3, w.s([d['rea']], 'eqcomd', '( %s -> P = ( Re ` %s ) )' % (A0, CA))], 'breqtrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, CA))
hyp = w.s([w.s([k1, k2], 'jca', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, CA, CB, CA, CB)), k3], 'jca',
          '( %s -> ( ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ 0 < ( Re ` %s ) ) )' % (A0, CA, CB, CA, CB, CA))
rid = w.s([w.s([urp, w.s([d['ac'], d['bc']], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CA, CB))], 'jca',
               '( %s -> ( U e. RR+ /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, CA, CB)), hyp, w.inst('pkrecid0')], 'syl2anc',
          '( %s -> ( %s rectint <. %s , %s >. ) = 0 )' % (A0, PK0, CA, CB))
w.qed([d['rco'], rid], 'eqtr3d', '( %s -> %s = 0 )' % (A0, FOUR(PK0, 'P', 'Q', 'S', 'R')))
run7(w)

# ---------------------------------------------------------------- farabs
A0 = '( %s /\\ T e. RR+ )' % UGT1
G = '( ( T ^ 2 ) x. %s )' % LGU
G1 = '( %s + 1 )' % G
LG1 = '( log ` %s )' % G1
QQ = '( %s / %s )' % (LG1, LGU)
w = W('farabs', 'The far abscissa of Perron\'s contour for ` 1 < U `: it is at least ` 1 ` and '
      '` U ` raised to it dominates ` T ^ 2 log U ` (Lean\'s ` max ` replaced by the sum of '
      'the two nonnegative candidates).')
ur = w.s([], 'simpll', '( %s -> U e. RR )' % A0)
u1 = w.s([], 'simplr', '( %s -> 1 < U )' % A0)
trp = w.s([], 'simpr', '( %s -> T e. RR+ )' % A0)
lrp = w.s([ur, u1, w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A0, LGU))
u0 = w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), ur, a1(w, A0, '0lt1', '0 < 1'), u1], 'lttrd', '( %s -> 0 < U )' % A0)
urp = w.s([ur, u0], 'elrpd', '( %s -> U e. RR+ )' % A0)
t2 = w.s([trp, a1(w, A0, '2z', '2 e. ZZ')], 'rpexpcld', '( %s -> ( T ^ 2 ) e. RR+ )' % A0)
grp = w.s([t2, lrp], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, G))
g1rp = w.s([grp, a1(w, A0, '1rp', '1 e. RR+')], 'rpaddcld', '( %s -> %s e. RR+ )' % (A0, G1))
cl = Closure(w, A0, {'U': ('RR+', urp), 'T': ('RR+', trp), LGU: ('RR+', lrp), G: ('RR+', grp), G1: ('RR+', g1rp)})
gr = cl.mem(G, 'RR'); g1r = cl.mem(G1, 'RR'); lr = cl.mem(LGU, 'RR')
g1ge1 = linarith(w, A0, [cl.gt0(G)], '1 <_ %s' % G1, closure=cl)
lg1r = cl.mem(LG1, 'RR')
lg10 = w.s([g1r, g1ge1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (A0, LG1))
q0 = w.s([lg1r, lrp, lg10], 'divge0d', '( %s -> 0 <_ %s )' % (A0, QQ))
cl.atom(QQ); qr = cl.mem(QQ, 'RR')
c1 = linarith(w, A0, [q0], '1 <_ %s' % FA, closure=cl)
# U ^c FA = exp ( FA x. L )
far = cl.mem(FA, 'RR'); fac = w.s([far], 'recnd', '( %s -> %s e. CC )' % (A0, FA))
cef = w.s([w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0), w.s([urp], 'rpne0d', '( %s -> U =/= 0 )' % A0), fac, w.inst('cxpef')], 'syl3anc',
          '( %s -> ( U ^c %s ) = ( exp ` ( %s x. %s ) ) )' % (A0, FA, FA, LGU))
lc = w.s([lr], 'recnd', '( %s -> %s e. CC )' % (A0, LGU)); qc = w.s([qr], 'recnd', '( %s -> %s e. CC )' % (A0, QQ))
lg1c = w.s([lg1r], 'recnd', '( %s -> %s e. CC )' % (A0, LG1))
m1 = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), qc, lc], 'adddird', '( %s -> ( ( 1 + %s ) x. %s ) = ( ( 1 x. %s ) + ( %s x. %s ) ) )' % (A0, QQ, LGU, LGU, QQ, LGU))
m2 = w.s([w.s([lc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, LGU, LGU)),
          w.s([lg1c, lc, w.s([lrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, LGU))], 'divcan1d', '( %s -> ( %s x. %s ) = %s )' % (A0, QQ, LGU, LG1))], 'oveq12d',
         '( %s -> ( ( 1 x. %s ) + ( %s x. %s ) ) = ( %s + %s ) )' % (A0, LGU, QQ, LGU, LGU, LG1))
meq = w.s([m1, m2], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s + %s ) )' % (A0, FA, LGU, LGU, LG1))
ile = linarith(w, A0, [cl.gt0(LGU)], '%s <_ ( %s + %s )' % (LG1, LGU, LG1), closure=cl)
sumr = cl.mem('( %s + %s )' % (LGU, LG1), 'RR')
bi = w.s([lg1r, sumr, w.inst('efle')], 'syl2anc', '( %s -> ( %s <_ ( %s + %s ) <-> ( exp ` %s ) <_ ( exp ` ( %s + %s ) ) ) )' % (A0, LG1, LGU, LG1, LG1, LGU, LG1))
ele = w.s([ile, bi], 'mpbid', '( %s -> ( exp ` %s ) <_ ( exp ` ( %s + %s ) ) )' % (A0, LG1, LGU, LG1))
efl = w.s([g1rp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = %s )' % (A0, LG1, G1))
gle = linarith(w, A0, [], '%s <_ %s' % (G, G1), closure=cl)
ch1 = w.s([gle, w.s([efl], 'eqcomd', '( %s -> %s = ( exp ` %s ) )' % (A0, G1, LG1))], 'breqtrd', '( %s -> %s <_ ( exp ` %s ) )' % (A0, G, LG1))
efr1 = w.s([lg1r], 'reefcld', '( %s -> ( exp ` %s ) e. RR )' % (A0, LG1))
efr2 = w.s([sumr], 'reefcld', '( %s -> ( exp ` ( %s + %s ) ) e. RR )' % (A0, LGU, LG1))
ch2 = w.s([gr, efr1, efr2, ch1, ele], 'letrd', '( %s -> %s <_ ( exp ` ( %s + %s ) ) )' % (A0, G, LGU, LG1))
ch3 = w.s([ch2, w.s([w.s([meq], 'eqcomd', '( %s -> ( %s + %s ) = ( %s x. %s ) )' % (A0, LGU, LG1, FA, LGU))], 'fveq2d',
                     '( %s -> ( exp ` ( %s + %s ) ) = ( exp ` ( %s x. %s ) ) )' % (A0, LGU, LG1, FA, LGU))], 'breqtrd',
          '( %s -> %s <_ ( exp ` ( %s x. %s ) ) )' % (A0, G, FA, LGU))
c2 = w.s([ch3, w.s([cef], 'eqcomd', '( %s -> ( exp ` ( %s x. %s ) ) = ( U ^c %s ) )' % (A0, FA, LGU, FA))], 'breqtrd', '( %s -> %s <_ ( U ^c %s ) )' % (A0, G, FA))
w.qed([c1, c2], 'jca', '( %s -> ( 1 <_ %s /\\ %s <_ ( U ^c %s ) ) )' % (A0, FA, G, FA))
run7(w)

# ---------------------------------------------------------------- farabs0
A0 = '( %s /\\ %s )' % (ULT1, CT)
G = '( ( T ^ 2 ) x. %s )' % NLGU
G1 = '( %s + 1 )' % G
LG1 = '( log ` %s )' % G1
QQ = '( %s / %s )' % (LG1, NLGU)
D = '( %s - C )' % FB
w = W('farabs0', 'The far abscissa of Perron\'s contour for ` U < 1 `: it exceeds ` C + 1 ` and '
      '` U ` raised to it is at most ` ( U ^c C ) / ( T ^ 2 |log U| ) `.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0)
u1 = w.s([], 'simplr', '( %s -> U < 1 )' % A0)
crp = w.s([], 'simprl', '( %s -> C e. RR+ )' % A0)
trp = w.s([], 'simprr', '( %s -> T e. RR+ )' % A0)
lr = w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, LGU))
bi = w.s([urp, a1(w, A0, '1rp', '1 e. RR+'), w.inst('logltb')], 'syl2anc', '( %s -> ( U < 1 <-> %s < ( log ` 1 ) ) )' % (A0, LGU))
l1 = w.s([u1, bi], 'mpbid', '( %s -> %s < ( log ` 1 ) )' % (A0, LGU))
l0 = w.s([l1, a1(w, A0, 'log1', '( log ` 1 ) = 0')], 'breqtrd', '( %s -> %s < 0 )' % (A0, LGU))
nlrp = w.s([l0, w.s([lr, w.inst('negelrp')], 'syl', '( %s -> ( %s e. RR+ <-> %s < 0 ) )' % (A0, NLGU, LGU))], 'mpbird', '( %s -> %s e. RR+ )' % (A0, NLGU))
t2 = w.s([trp, a1(w, A0, '2z', '2 e. ZZ')], 'rpexpcld', '( %s -> ( T ^ 2 ) e. RR+ )' % A0)
grp = w.s([t2, nlrp], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, G))
g1rp = w.s([grp, a1(w, A0, '1rp', '1 e. RR+')], 'rpaddcld', '( %s -> %s e. RR+ )' % (A0, G1))
cl = Closure(w, A0, {'U': ('RR+', urp), 'T': ('RR+', trp), 'C': ('RR+', crp), LGU: [('RR', lr)], NLGU: ('RR+', nlrp), G: ('RR+', grp), G1: ('RR+', g1rp)})
cl.atom(LGU); cl.atom(NLGU)
gr = cl.mem(G, 'RR'); g1r = cl.mem(G1, 'RR')
g1ge1 = linarith(w, A0, [cl.gt0(G)], '1 <_ %s' % G1, closure=cl)
lg1r = cl.mem(LG1, 'RR')
lg10 = w.s([g1r, g1ge1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (A0, LG1))
q0 = w.s([lg1r, nlrp, lg10], 'divge0d', '( %s -> 0 <_ %s )' % (A0, QQ))
cl.atom(QQ); qr = cl.mem(QQ, 'RR')
cr = cl.mem('C', 'RR')
c1 = linarith(w, A0, [q0], '( C + 1 ) <_ %s' % FB, closure=cl)
# FB = C + D and U ^c FB = U ^c C x. U ^c D
fbr = cl.mem(FB, 'RR'); fbc = w.s([fbr], 'recnd', '( %s -> %s e. CC )' % (A0, FB)); cc = w.s([cr], 'recnd', '( %s -> C e. CC )' % A0)
dr = cl.mem(D, 'RR'); dc = w.s([dr], 'recnd', '( %s -> %s e. CC )' % (A0, D))
fbeq = w.s([cc, fbc], 'pncan3d', '( %s -> ( C + %s ) = %s )' % (A0, D, FB))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0); une = w.s([urp], 'rpne0d', '( %s -> U =/= 0 )' % A0)
spl = w.s([uc, une, cc, dc], 'cxpaddd', '( %s -> ( U ^c ( C + %s ) ) = ( ( U ^c C ) x. ( U ^c %s ) ) )' % (A0, D, D))
spl2 = w.s([w.s([w.s([fbeq], 'eqcomd', '( %s -> %s = ( C + %s ) )' % (A0, FB, D))], 'oveq2d', '( %s -> ( U ^c %s ) = ( U ^c ( C + %s ) ) )' % (A0, FB, D)), spl], 'eqtrd',
           '( %s -> ( U ^c %s ) = ( ( U ^c C ) x. ( U ^c %s ) ) )' % (A0, FB, D))
# U ^c D = exp ( D x. L ), D x. L = L - log G1
cef = w.s([uc, une, dc, w.inst('cxpef')], 'syl3anc', '( %s -> ( U ^c %s ) = ( exp ` ( %s x. %s ) ) )' % (A0, D, D, LGU))
deq = lineq(w, A0, D, '( 1 + %s )' % QQ, closure=cl)
lc = w.s([lr], 'recnd', '( %s -> %s e. CC )' % (A0, LGU)); qc = w.s([qr], 'recnd', '( %s -> %s e. CC )' % (A0, QQ))
lg1c = w.s([lg1r], 'recnd', '( %s -> %s e. CC )' % (A0, LG1))
lne = w.s([l0], 'lt0ne0d', '( %s -> %s =/= 0 )' % (A0, LGU))
# ( QQ x. L ) = -u LG1 :  QQ = LG1 / -u L = -u ( LG1 / L )
qneg2 = w.s([lg1c, lc, lne], 'divneg2d', '( %s -> -u ( %s / %s ) = %s )' % (A0, LG1, LGU, QQ))
ql = w.s([w.s([w.s([qneg2], 'eqcomd', '( %s -> %s = -u ( %s / %s ) )' % (A0, QQ, LG1, LGU))], 'oveq1d', '( %s -> ( %s x. %s ) = ( -u ( %s / %s ) x. %s ) )' % (A0, QQ, LGU, LG1, LGU, LGU)),
           w.s([w.s([w.s([lg1c, lc, lne], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, LG1, LGU)), lc], 'mulneg1d', '( %s -> ( -u ( %s / %s ) x. %s ) = -u ( ( %s / %s ) x. %s ) )' % (A0, LG1, LGU, LGU, LG1, LGU, LGU)),
                w.s([w.s([lg1c, lc, lne], 'divcan1d', '( %s -> ( ( %s / %s ) x. %s ) = %s )' % (A0, LG1, LGU, LGU, LG1))], 'negeqd', '( %s -> -u ( ( %s / %s ) x. %s ) = -u %s )' % (A0, LG1, LGU, LGU, LG1))],
               'eqtrd', '( %s -> ( -u ( %s / %s ) x. %s ) = -u %s )' % (A0, LG1, LGU, LGU, LG1))], 'eqtrd', '( %s -> ( %s x. %s ) = -u %s )' % (A0, QQ, LGU, LG1))
dl1 = w.s([w.s([deq], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( 1 + %s ) x. %s ) )' % (A0, D, LGU, QQ, LGU)),
           w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), qc, lc], 'adddird', '( %s -> ( ( 1 + %s ) x. %s ) = ( ( 1 x. %s ) + ( %s x. %s ) ) )' % (A0, QQ, LGU, LGU, QQ, LGU))], 'eqtrd',
          '( %s -> ( %s x. %s ) = ( ( 1 x. %s ) + ( %s x. %s ) ) )' % (A0, D, LGU, LGU, QQ, LGU))
dl2 = w.s([dl1, w.s([w.s([lc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, LGU, LGU)), ql], 'oveq12d', '( %s -> ( ( 1 x. %s ) + ( %s x. %s ) ) = ( %s + -u %s ) )' % (A0, LGU, QQ, LGU, LGU, LG1))],
          'eqtrd', '( %s -> ( %s x. %s ) = ( %s + -u %s ) )' % (A0, D, LGU, LGU, LG1))
dlr = cl.mem('( %s + -u %s )' % (LGU, LG1), 'RR')
ile = linarith(w, A0, [l0], '( %s + -u %s ) <_ -u %s' % (LGU, LG1, LG1), closure=cl)
nlg1r = cl.mem('-u %s' % LG1, 'RR')
bi = w.s([dlr, nlg1r, w.inst('efle')], 'syl2anc', '( %s -> ( ( %s + -u %s ) <_ -u %s <-> ( exp ` ( %s + -u %s ) ) <_ ( exp ` -u %s ) ) )' % (A0, LGU, LG1, LG1, LGU, LG1, LG1))
ele = w.s([ile, bi], 'mpbid', '( %s -> ( exp ` ( %s + -u %s ) ) <_ ( exp ` -u %s ) )' % (A0, LGU, LG1, LG1))
efn = w.s([lg1c, w.inst('efneg')], 'syl', '( %s -> ( exp ` -u %s ) = ( 1 / ( exp ` %s ) ) )' % (A0, LG1, LG1))
efl = w.s([g1rp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = %s )' % (A0, LG1, G1))
efn2 = w.s([efn, w.s([efl], 'oveq2d', '( %s -> ( 1 / ( exp ` %s ) ) = ( 1 / %s ) )' % (A0, LG1, G1))], 'eqtrd', '( %s -> ( exp ` -u %s ) = ( 1 / %s ) )' % (A0, LG1, G1))
gle = linarith(w, A0, [], '%s <_ %s' % (G, G1), closure=cl)
rec = w.s([grp, g1rp, a1(w, A0, '1re', '1 e. RR'), a1(w, A0, '0le1', '0 <_ 1'), gle], 'lediv2ad', '( %s -> ( 1 / %s ) <_ ( 1 / %s ) )' % (A0, G1, G))
udv = w.s([w.s([cef, w.s([dl2], 'fveq2d', '( %s -> ( exp ` ( %s x. %s ) ) = ( exp ` ( %s + -u %s ) ) )' % (A0, D, LGU, LGU, LG1))], 'eqtrd',
                '( %s -> ( U ^c %s ) = ( exp ` ( %s + -u %s ) ) )' % (A0, D, LGU, LG1)),
           w.s([ele, efn2], 'breqtrd', '( %s -> ( exp ` ( %s + -u %s ) ) <_ ( 1 / %s ) )' % (A0, LGU, LG1, G1))], 'eqbrtrd',
          '( %s -> ( U ^c %s ) <_ ( 1 / %s ) )' % (A0, D, G1))
r1 = w.s([w.s([urp, dr], 'rpcxpcld', '( %s -> ( U ^c %s ) e. RR+ )' % (A0, D))], 'rpred', '( %s -> ( U ^c %s ) e. RR )' % (A0, D))
rg1 = w.s([w.s([g1rp], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (A0, G1))], 'rpred', '( %s -> ( 1 / %s ) e. RR )' % (A0, G1))
rg = w.s([w.s([grp], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (A0, G))], 'rpred', '( %s -> ( 1 / %s ) e. RR )' % (A0, G))
udv2 = w.s([r1, rg1, rg, udv, rec], 'letrd', '( %s -> ( U ^c %s ) <_ ( 1 / %s ) )' % (A0, D, G))
ucrp = w.s([urp, cr], 'rpcxpcld', '( %s -> ( U ^c C ) e. RR+ )' % A0)
mul = w.s([r1, rg, w.s([ucrp], 'rpred', '( %s -> ( U ^c C ) e. RR )' % A0), w.s([ucrp], 'rpge0d', '( %s -> 0 <_ ( U ^c C ) )' % A0), udv2], 'lemul2ad',
          '( %s -> ( ( U ^c C ) x. ( U ^c %s ) ) <_ ( ( U ^c C ) x. ( 1 / %s ) ) )' % (A0, D, G))
dvr = w.s([w.s([ucrp], 'rpcnd', '( %s -> ( U ^c C ) e. CC )' % A0), w.s([grp], 'rpcnd', '( %s -> %s e. CC )' % (A0, G)), w.s([grp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, G))],
          'divrecd', '( %s -> ( ( U ^c C ) / %s ) = ( ( U ^c C ) x. ( 1 / %s ) ) )' % (A0, G, G))
c2 = w.s([spl2, w.s([mul, w.s([dvr], 'eqcomd', '( %s -> ( ( U ^c C ) x. ( 1 / %s ) ) = ( ( U ^c C ) / %s ) )' % (A0, G, G))], 'breqtrd',
                          '( %s -> ( ( U ^c C ) x. ( U ^c %s ) ) <_ ( ( U ^c C ) / %s ) )' % (A0, D, G))], 'eqbrtrd',
         '( %s -> ( U ^c %s ) <_ ( ( U ^c C ) / %s ) )' % (A0, FB, G))
w.qed([c1, c2], 'jca', '( %s -> ( ( C + 1 ) <_ %s /\\ ( U ^c %s ) <_ ( ( U ^c C ) / %s ) ) )' % (A0, FB, FB, G))
run7(w)
