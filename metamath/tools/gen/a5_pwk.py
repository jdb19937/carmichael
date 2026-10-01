"""Sortie A5, batch 10: the pointwise core at a fixed accepted shift (Lean:
the body of search_successW_of after step 3 has produced k0).
MM_DB=sorties/a5.mm python3 tools/gen/a5_pwk.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a5lib
from tm import *
from a2lib import WH
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

GW = '( ( Z goodPrimesW W ) ` Y )'
LQ = '( Lmod ` ran Q )'
XQ = '( xceil ` ran Q )'
NSQ = '( Nstar ` ran Q )'
PW = '( ( log ` N ) ^c ( 6 / 5 ) )'
X5 = '( A ^ 5 )'
PRDQ = 'prod_ i e. ( 0 ..^ ( # ` Q ) ) ( Q ` i )'
R1 = '( 1st ` R )'
SCN = '( ( ( ( ( Q Scan %s ) ` Z ) ` H ) ` 1 ) ` %s )' % (X5, X5)
KJ = '( 1st ` ( 2nd ` ( 1st ` J ) ) )'
PJ = '( 2nd ` ( 2nd ` ( 1st ` J ) ) )'
MX = '( 1st ` ( 2nd ` ( 1st ` X ) ) )'
SX = '( 2nd ` ( 2nd ` ( 1st ` X ) ) )'
POOL = lambda k: '( ( ran Q pool Z ) ` %s )' % k
PLA = lambda k: '( 1st ` ( ( ( Q PoolAlg %s ) ` Z ) ` %s ) )' % (X5, k)
CB = lambda t, k: '( %s x. ( ( %s + 2 ) + ( ( 2 ^ %s ) x. ( ( Nfloor ` ( sqrt ` %s ) ) + 3 ) ) ) )' % (k, t, t, X5)
def PRD(s, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, s, s, i)
PJS = 'prod_ j e. ran %s j' % SX
SC = '<. <. <. Z , W >. , <. Y , T >. >. , H >.'
SR = '( %s Search N )' % SC
MMR = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % SR
SSR = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % SR
CARM = lambda m: '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (m, m, m, m)
EXPB = '( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) )'
PROD = '( ProdL ` Q )'
CC = '( ( ( ( 2nd ` R ) + T ) + ( 2nd ` %s ) ) + 2 )' % PROD
CTT = '( ( ( ( 2nd ` R ) + T ) + T ) + 2 )'
COSTEX = '( ( ( %s + ( 2nd ` J ) ) + ( 2nd ` X ) ) + ( 2nd ` U ) )' % CTT
CSUM = '( ( ( %s + ( 2nd ` J ) ) + ( 2nd ` X ) ) + ( 2nd ` U ) )' % CC
CP = '( ( ( ( ( ( ( Z CostPieces Y ) ` T ) ` A ) ` %s ) ` %s ) ` ( # ` P ) ) ` ( # ` %s ) )' % (X5, KJ, SX)

EXTRB = a5lib.winbody('extrwinputs')
OUTB = a5lib.winbody('outwcarm')
COSTB = a5lib.winbody('costpiecesle')

CONCL = ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
         '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
         '( %s = %s /\\ %s /\\ ( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) ) ) /\\ '
         '( 2nd ` %s ) <_ %s )'
         % (SR, SSR, SSR, SSR, MMR, PRD(SSR), CARM(MMR), MMR, MMR, SR, EXPB))


BTEXTS = [
    '( 1st ` J ) =/= ( inr ` (/) )',
    '%s e. NN' % KJ,
    '%s <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) )' % (KJ, X5),
    '( 2nd ` J ) <_ %s' % CB('( # ` Q )', KJ),
    'P e. Word NN0',
    'ran P = %s' % POOL(KJ),
    '( # ` P ) = ( # ` %s )' % POOL(KJ),
    'A. b e. ran P ( 2 <_ b /\\ b <_ %s )' % X5,
    '( 1st ` X ) =/= ( inr ` (/) )',
    '%s e. NN0' % MX,
    '%s e. Word NN0' % SX,
    'Fun `\' %s' % SX,
    'ran %s C_ ran P' % SX,
    '%s = %s' % (PRD(SX), MX),
    'N < %s' % MX,
    '( 2nd ` X ) <_ ( ( ( # ` P ) x. ( A + 3 ) ) + 1 )',
    'A. b e. ran %s b e. Prime' % SX,
    '3 <_ ( # ` %s )' % SX,
    CARM(MX),
    '%s <_ ( N ^c ( 1 + D ) )' % MX,
    '( 1st ` U ) = 1o',
]
BUN = a5lib.bundletext(BTEXTS)

w = WH('a5pka', 'Steps 3 to 5 of the search at a tuple of scales in the window: the accepted shift, the extraction and the output certificate (Lean: SearchAlg.lean lines 141-215).')
h1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
h2 = w.h('( T e. NN0 /\\ H e. NN0 )')
h3 = w.h('N e. ( ZZ>= ` 3 )')
h4 = w.h('R = ( ( Z Reservoir W ) ` Y )')
h5 = w.h('I = ( # ` %s )' % R1)
h6 = w.h('Q = ( %s substr <. ( I - T ) , I >. )' % R1)
h7 = w.h('A = %s' % PRDQ)
h8 = w.h('J = %s' % SCN)
h9 = w.h('P = %s' % PJ)
h10 = w.h('X = ( ( A Extract N ) ` P )')
h11 = w.h('U = ( %s Verify %s )' % (MX, SX))
h12 = w.h('T <_ ( # ` %s )' % GW)
h13 = w.h('( %s <_ H /\\ H <_ ( ; 1 6 x. %s ) )' % (PW, PW))
h14 = w.h('K e. NN')
h15 = w.h('( ( K <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) /\\ ( K gcd %s ) = 1 ) /\\ ( ; 1 6 x. %s ) <_ ( # ` %s ) )'
          % (XQ, LQ, PW, POOL('K')))
h16 = w.h(EXTRB)
h17 = w.h(OUTB)
h18 = w.h(COSTB)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
lit = lambda t, k: w.s([num.fact(w, t, k)], 'a1i', '( ph -> %s )' % (('%s e. %s' % (t, k)) if k in ('RR', 'NN0', 'NN', 'CC', 'RR+', 'ZZ') else {'ge0': '0 <_ %s' % t, 'gt0': '0 < %s' % t}[k]))

# ---------------------------------------------------------------- typing
znn = st([h1], 'simp1d', 'Z e. NN')
wn0 = st([h1], 'simp2d', 'W e. NN0')
ynn = st([h1], 'simp3d', 'Y e. NN')
tn0 = st([h2], 'simpld', 'T e. NN0')
hn0 = st([h2], 'simprd', 'H e. NN0')
zn0 = st([znn], 'nnnn0d', 'Z e. NN0')
nn0 = st([lit('3', 'NN0'), h3, w.inst('eluznn0')], 'syl2anc', 'N e. NN0')
n3le = st([h3, w.inst('eluzle')], 'syl', '3 <_ N')
nre = st([nn0], 'nn0red', 'N e. RR')
n1le = st([lit('1', 'RR'), lit('3', 'RR'), nre, st([w.s([], '1le3', '1 <_ 3')], 'a1i', '1 <_ 3'), n3le],
          'letrd', '1 <_ N')

# ---------------------------------------------------------------- step 2
ti = w.s([h1, h4, h5, h12], 'a5ti', '( ph -> T <_ I )')
QB = ('( ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) ) /\\ '
      '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) )' % GW)
qb = w.s([h1, tn0, h4, h5, h6, ti], 'a5q', '( ph -> %s )' % QB)
qb1 = st([qb], 'simpld', '( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) )')
qb2 = st([qb], 'simprd', '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % GW)
qcl = st([st([qb1], 'simpld', '( Q e. Word NN0 /\\ Fun `\' Q )')], 'simpld', 'Q e. Word NN0')
qfun = st([st([qb1], 'simpld', '( Q e. Word NN0 /\\ Fun `\' Q )')], 'simprd', 'Fun `\' Q')
qlen = st([st([qb1], 'simprd', '( ( # ` Q ) = T /\\ ( # ` ran Q ) = T )')], 'simpld', '( # ` Q ) = T')
qcard = st([st([qb1], 'simprd', '( ( # ` Q ) = T /\\ ( # ` ran Q ) = T )')], 'simprd', '( # ` ran Q ) = T')
qss = st([st([qb2], 'simpld', '( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) )' % GW)], 'simpld', 'ran Q C_ %s' % GW)
qfp = st([st([qb2], 'simpld', '( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) )' % GW)], 'simprd',
         'ran Q e. ( ~P Prime i^i Fin )')
qall = st([qb2], 'simprd', 'A. c e. ran Q ( c e. Prime /\\ c <_ Z )')
ANC = '( ph /\\ c e. ran Q )'
cpr = w.s([w.s([w.s([qall], 'adantr', '( %s -> A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % ANC),
                w.s([], 'simpr', '( %s -> c e. ran Q )' % ANC), w.inst('rspa')], 'syl2anc',
               '( %s -> ( c e. Prime /\\ c <_ Z ) )' % ANC)], 'simpld', '( %s -> c e. Prime )' % ANC)
qprm = w.s([cpr], 'ralrimiva', '( ph -> A. c e. ran Q c e. Prime )')
QA = '( ( A e. NN /\\ %s e. NN ) /\\ ( %s = A /\\ %s = %s ) /\\ A <_ ( Z ^ T ) )' % (X5, LQ, XQ, X5)
qfp2 = st([qcl, qfun], 'jca', '( Q e. Word NN0 /\\ Fun `\' Q )')
qa = w.s([qfp2, st([zn0, tn0], 'jca', '( Z e. NN0 /\\ T e. NN0 )'), qlen, qall, h7], 'a5qa', '( ph -> %s )' % QA)
ann = st([st([qa], 'simp1d', '( A e. NN /\\ %s e. NN )' % X5)], 'simpld', 'A e. NN')
x5n = st([st([qa], 'simp1d', '( A e. NN /\\ %s e. NN )' % X5)], 'simprd', '%s e. NN' % X5)
x5n0 = st([x5n], 'nnnn0d', '%s e. NN0' % X5)
lmeq = st([st([qa], 'simp2d', '( %s = A /\\ %s = %s )' % (LQ, XQ, X5))], 'simpld', '%s = A' % LQ)
xceq = st([st([qa], 'simp2d', '( %s = A /\\ %s = %s )' % (LQ, XQ, X5))], 'simprd', '%s = %s' % (XQ, X5))
azt = st([qa], 'simp3d', 'A <_ ( Z ^ T )')
q3 = st([qcl, qfun, qprm], '3jca', '( Q e. Word NN0 /\\ Fun `\' Q /\\ A. c e. ran Q c e. Prime )')

# ---------------------------------------------------------------- step 3 at K
kbnd = st([h15], 'simpld', '( K <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) /\\ ( K gcd %s ) = 1 )' % (XQ, LQ))
kx = st([kbnd], 'simpld', 'K <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) )' % XQ)
kgcd = st([kbnd], 'simprd', '( K gcd %s ) = 1' % LQ)
kx2 = st([kx, w.s([xceq], 'oveq1d', '( ph -> ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) = ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) )' % (XQ, X5))],
         'breqtrd', 'K <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) )' % X5)
kf = w.s([ann, h14, kx2], 'a5kf', '( ph -> K <_ %s )' % X5)
kga = st([w.s([lmeq], 'oveq2d', '( ph -> ( K gcd %s ) = ( K gcd A ) )' % LQ), kgcd], 'eqtr3d', '( K gcd A ) = 1')
qcp = st([qcl, qprm], 'jca', '( Q e. Word NN0 /\\ A. c e. ran Q c e. Prime )')
kcop = st([kga, w.s([qcp, h14, h7], 'a5kc',
                    '( ph -> ( ( 1st ` ( Q CoprimeTo K ) ) = 1o <-> ( K gcd A ) = 1 ) )')], 'mpbird',
          '( 1st ` ( Q CoprimeTo K ) ) = 1o')
KPB = lambda k: ('( ( %s e. Word NN0 /\\ Fun `\' %s ) /\\ ( ran %s = %s /\\ ( # ` %s ) = ( # ` %s ) ) )'
                 % (PLA(k), PLA(k), PLA(k), POOL(k), PLA(k), POOL(k)))
kpb = w.s([q3, st([zn0, st([h14], 'nnnn0d', 'K e. NN0')], 'jca', '( Z e. NN0 /\\ K e. NN0 )'), h7, x5n0], 'a5kp',
          '( ph -> %s )' % KPB('K'))
pkw = st([st([kpb], 'simpld', '( %s e. Word NN0 /\\ Fun `\' %s )' % (PLA('K'), PLA('K')))], 'simpld',
         '%s e. Word NN0' % PLA('K'))
pkcard = st([st([kpb], 'simprd', '( ran %s = %s /\\ ( # ` %s ) = ( # ` %s ) )' % (PLA('K'), POOL('K'), PLA('K'), POOL('K')))],
            'simprd', '( # ` %s ) = ( # ` %s )' % (PLA('K'), POOL('K')))
pwh = st([h13], 'simpld', '%s <_ H' % PW)
hp16 = st([h13], 'simprd', 'H <_ ( ; 1 6 x. %s )' % PW)
hpool = st([h15], 'simprd', '( ; 1 6 x. %s ) <_ ( # ` %s )' % (PW, POOL('K')))
nuz2 = st([h3, w.inst('uzuzle23')], 'syl', 'N e. ( ZZ>= ` 2 )')
nnn = st([nuz2, w.inst('eluz2nn')], 'syl', 'N e. NN')
lognre = st([st([nnn], 'nnrpd', 'N e. RR+')], 'relogcld', '( log ` N ) e. RR')
logn0 = st([nre, n1le, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` N )')
pwre = st([lognre, logn0, lit('( 6 / 5 )', 'RR')], 'recxpcld', '%s e. RR' % PW)
p16re = st([lit('; 1 6', 'RR'), pwre], 'remulcld', '( ; 1 6 x. %s ) e. RR' % PW)
hre = st([hn0], 'nn0red', 'H e. RR')
plkre = st([st([pkw, w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % PLA('K'))], 'nn0red', '( # ` %s ) e. RR' % PLA('K'))
pokre = st([pkcard, plkre], 'eqeltrrd', '( # ` %s ) e. RR' % POOL('K'))
hlek = st([st([hre, p16re, pokre, hp16, hpool], 'letrd', 'H <_ ( # ` %s )' % POOL('K')),
           st([pkcard], 'eqcomd', '( # ` %s ) = ( # ` %s )' % (POOL('K'), PLA('K')))], 'breqtrd',
          'H <_ ( # ` %s )' % PLA('K'))
KS = ('( ( ( ( 1st ` J ) =/= ( inr ` (/) ) /\\ ( %s e. NN /\\ %s <_ K ) ) /\\ ( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o ) ) /\\ '
      '( ( H <_ ( # ` %s ) /\\ %s = %s ) /\\ ( 2nd ` J ) <_ %s ) )'
      % (KJ, KJ, PJ, KJ, PJ, PJ, PLA(KJ), CB('( # ` Q )', KJ)))
ks = w.s([st([qcl, zn0, hn0], '3jca', '( Q e. Word NN0 /\\ Z e. NN0 /\\ H e. NN0 )'),
          st([h14, x5n0], 'jca', '( K e. NN /\\ %s e. NN0 )' % X5), kf, kcop, hlek, h8], 'a5ks',
         '( ph -> %s )' % KS)
ksa = st([ks], 'simpld', '( ( ( 1st ` J ) =/= ( inr ` (/) ) /\\ ( %s e. NN /\\ %s <_ K ) ) /\\ ( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o ) )' % (KJ, KJ, PJ, KJ))
ksb = st([ks], 'simprd', '( ( H <_ ( # ` %s ) /\\ %s = %s ) /\\ ( 2nd ` J ) <_ %s )' % (PJ, PJ, PLA(KJ), CB('( # ` Q )', KJ)))
ksa1 = st([ksa], 'simpld', '( ( 1st ` J ) =/= ( inr ` (/) ) /\\ ( %s e. NN /\\ %s <_ K ) )' % (KJ, KJ))
jne = st([ksa1], 'simpld', '( 1st ` J ) =/= ( inr ` (/) )')
kknn = st([st([ksa1], 'simprd', '( %s e. NN /\\ %s <_ K )' % (KJ, KJ))], 'simpld', '%s e. NN' % KJ)
kkle = st([st([ksa1], 'simprd', '( %s e. NN /\\ %s <_ K )' % (KJ, KJ))], 'simprd', '%s <_ K' % KJ)
pjw = st([st([ksa], 'simprd', '( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o )' % (PJ, KJ))], 'simpld',
         '%s e. Word NN0' % PJ)
jcop = st([st([ksa], 'simprd', '( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o )' % (PJ, KJ))], 'simprd',
          '( 1st ` ( Q CoprimeTo %s ) ) = 1o' % KJ)
jh = st([st([ksb], 'simpld', '( H <_ ( # ` %s ) /\\ %s = %s )' % (PJ, PJ, PLA(KJ)))], 'simpld', 'H <_ ( # ` %s )' % PJ)
jpd = st([st([ksb], 'simpld', '( H <_ ( # ` %s ) /\\ %s = %s )' % (PJ, PJ, PLA(KJ)))], 'simprd', '%s = %s' % (PJ, PLA(KJ)))
jcst = st([ksb], 'simprd', '( 2nd ` J ) <_ %s' % CB('( # ` Q )', KJ))
# transfer to P
plen = w.s([h9], 'fveq2d', '( ph -> ( # ` P ) = ( # ` %s ) )' % PJ)
pw = st([h9, pjw], 'eqeltrd', 'P e. Word NN0')
hlep = st([jh, plen], 'breqtrrd', 'H <_ ( # ` P )')
pdef = st([h9, jpd], 'eqtrd', 'P = %s' % PLA(KJ))
kkn0 = st([kknn], 'nnnn0d', '%s e. NN0' % KJ)
kpb2 = w.s([q3, st([zn0, kkn0], 'jca', '( Z e. NN0 /\\ %s e. NN0 )' % KJ), h7, x5n0], 'a5kp', '( ph -> %s )' % KPB(KJ))
pfun2 = st([st([kpb2], 'simpld', '( %s e. Word NN0 /\\ Fun `\' %s )' % (PLA(KJ), PLA(KJ)))], 'simprd',
           'Fun `\' %s' % PLA(KJ))
prn2 = st([st([kpb2], 'simprd', '( ran %s = %s /\\ ( # ` %s ) = ( # ` %s ) )' % (PLA(KJ), POOL(KJ), PLA(KJ), POOL(KJ)))],
          'simpld', 'ran %s = %s' % (PLA(KJ), POOL(KJ)))
pcard2 = st([st([kpb2], 'simprd', '( ran %s = %s /\\ ( # ` %s ) = ( # ` %s ) )' % (PLA(KJ), POOL(KJ), PLA(KJ), POOL(KJ)))],
            'simprd', '( # ` %s ) = ( # ` %s )' % (PLA(KJ), POOL(KJ)))
pfun = st([pfun2, w.s([w.s([pdef], 'cnveqd', '( ph -> `\' P = `\' %s )' % PLA(KJ))], 'funeqd',
                      '( ph -> ( Fun `\' P <-> Fun `\' %s ) )' % PLA(KJ))], 'mpbird', 'Fun `\' P')
prn = st([w.s([pdef], 'rneqd', '( ph -> ran P = ran %s )' % PLA(KJ)), prn2], 'eqtrd', 'ran P = %s' % POOL(KJ))
pcard = st([w.s([pdef], 'fveq2d', '( ph -> ( # ` P ) = ( # ` %s ) )' % PLA(KJ)), pcard2], 'eqtrd',
           '( # ` P ) = ( # ` %s )' % POOL(KJ))
kkcopa = st([jcop, w.s([qcp, kknn, h7], 'a5kc',
                       '( ph -> ( ( 1st ` ( Q CoprimeTo %s ) ) = 1o <-> ( %s gcd A ) = 1 ) )' % (KJ, KJ))], 'mpbid',
            '( %s gcd A ) = 1' % KJ)
kkcopl = st([w.s([lmeq], 'oveq2d', '( ph -> ( %s gcd %s ) = ( %s gcd A ) )' % (KJ, LQ, KJ)), kkcopa], 'eqtrd',
            '( %s gcd %s ) = 1' % (KJ, LQ))

# ------------------------------------------------- step 4: the extraction
rqv = st([qcl, w.inst('rnexg')], 'syl', 'ran Q e. _V')
rqpw = st([st([rqv, w.inst('elpwg')], 'syl', '( ran Q e. ~P %s <-> ran Q C_ %s )' % (GW, GW)), qss], 'mpbird',
          'ran Q e. ~P %s' % GW)
plre = st([st([pw, w.inst('lencl')], 'syl', '( # ` P ) e. NN0')], 'nn0red', '( # ` P ) e. RR')
pokre2 = st([pcard, plre], 'eqeltrrd', '( # ` %s ) e. RR' % POOL(KJ))
pwpool = st([st([pwre, hre, plre, pwh, hlep], 'letrd', '%s <_ ( # ` P )' % PW), pcard], 'breqtrd',
            '%s <_ ( # ` %s )' % (PW, POOL(KJ)))
inp, INP = a5lib.unwind(w, 'ph', h16, EXTRB,
                        [('q', 'q', '~P %s' % GW, 'ran Q', rqpw), ('m', qcard),
                         ('q', 'k', 'NN', KJ, kknn), ('m', kkcopl), ('m', pwpool)])
i1 = w.s([inp], 'simpld', '( ph -> ( ( 2 <_ %s /\\ 1 <_ %s ) /\\ A. p e. %s ( ( p e. Prime /\\ p <_ %s ) /\\ ( p gcd %s ) = 1 ) ) )'
         % (LQ, NSQ, POOL(KJ), XQ, LQ))
i2 = w.s([inp], 'simprd', '( ph -> ( ( ( ( ( %s + 1 ) Nlog N ) + 1 ) x. %s ) <_ ( # ` %s ) /\\ A. u e. ~P %s ( ( # ` u ) = %s -> E. s e. ~P u ( s =/= (/) /\\ %s || ( prod_ j e. s j - 1 ) ) ) ) )'
         % (LQ, NSQ, POOL(KJ), POOL(KJ), NSQ, LQ))
i2le = st([st([i1], 'simpld', '( 2 <_ %s /\\ 1 <_ %s )' % (LQ, NSQ))], 'simpld', '2 <_ %s' % LQ)
a2le = st([i2le, lmeq], 'breqtrd', '2 <_ A')
ipool = st([i1], 'simprd', 'A. p e. %s ( ( p e. Prime /\\ p <_ %s ) /\\ ( p gcd %s ) = 1 )' % (POOL(KJ), XQ, LQ))
isup = st([i2], 'simpld', '( ( ( ( %s + 1 ) Nlog N ) + 1 ) x. %s ) <_ ( # ` %s )' % (LQ, NSQ, POOL(KJ)))
IVEB = ('A. u e. ~P %s ( ( # ` u ) = %s -> E. s e. ~P u ( s =/= (/) /\\ %s || ( prod_ j e. s j - 1 ) ) )'
        % (POOL(KJ), NSQ, LQ))
iveb = st([i2], 'simprd', IVEB)
nsn = st([qfp, w.inst('nstarcl')], 'syl', '%s e. NN' % NSQ)
# every pool element is a prime at most ( A ^ 5 )
ANB = '( ph /\\ b e. ran P )'
bst = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (ANB, f))
bmem = bst([w.s([], 'simpr', '( %s -> b e. ran P )' % ANB),
            w.s([prn], 'adantr', '( %s -> ran P = %s )' % (ANB, POOL(KJ)))], 'eleqtrd', 'b e. %s' % POOL(KJ))
bp, BP = a5lib.unwind(w, ANB, w.s([ipool], 'adantr', '( %s -> %s )' % (ANB, 'A. p e. %s ( ( p e. Prime /\\ p <_ %s ) /\\ ( p gcd %s ) = 1 )' % (POOL(KJ), XQ, LQ))),
                      'A. p e. %s ( ( p e. Prime /\\ p <_ %s ) /\\ ( p gcd %s ) = 1 )' % (POOL(KJ), XQ, LQ),
                      [('q', 'p', POOL(KJ), 'b', bmem)])
bprm = bst([bst([bp], 'simpld', '( b e. Prime /\\ b <_ %s )' % XQ)], 'simpld', 'b e. Prime')
b2le = bst([bst([bprm, w.inst('prmuz2')], 'syl', 'b e. ( ZZ>= ` 2 )'), w.inst('eluzle')], 'syl', '2 <_ b')
bxle = bst([bst([bst([bp], 'simpld', '( b e. Prime /\\ b <_ %s )' % XQ)], 'simprd', 'b <_ %s' % XQ),
            w.s([xceq], 'adantr', '( %s -> %s = %s )' % (ANB, XQ, X5))], 'breqtrd', 'b <_ %s' % X5)
ball = w.s([bst([b2le, bxle], 'jca', '( 2 <_ b /\\ b <_ %s )' % X5)], 'ralrimiva',
           '( ph -> A. b e. ran P ( 2 <_ b /\\ b <_ %s ) )' % X5)
# the vEBK input at ran P and A
vebstep, VEB = a5lib.ccongr(w, 'ph', IVEB,
                            [(POOL(KJ), 'ran P', st([prn], 'eqcomd', '%s = ran P' % POOL(KJ))),
                             (LQ, 'A', lmeq)])
veb = st([iveb, vebstep], 'mpbid', VEB)
supA = st([st([isup, w.s([w.s([w.s([w.s([lmeq], 'oveq1d', '( ph -> ( %s + 1 ) = ( A + 1 ) )' % LQ)], 'oveq1d',
                               '( ph -> ( ( %s + 1 ) Nlog N ) = ( ( A + 1 ) Nlog N ) )' % LQ)], 'oveq1d',
                          '( ph -> ( ( ( %s + 1 ) Nlog N ) + 1 ) = ( ( ( A + 1 ) Nlog N ) + 1 ) )' % LQ)], 'oveq1d',
                     '( ph -> ( ( ( ( %s + 1 ) Nlog N ) + 1 ) x. %s ) = ( ( ( ( A + 1 ) Nlog N ) + 1 ) x. %s ) )' % (LQ, NSQ, NSQ))],
              'eqbrtrrd', '( ( ( ( A + 1 ) Nlog N ) + 1 ) x. %s ) <_ ( # ` %s )' % (NSQ, POOL(KJ))),
             st([pcard], 'eqcomd', '( # ` %s ) = ( # ` P )' % POOL(KJ))], 'breqtrd',
            '( ( ( ( A + 1 ) Nlog N ) + 1 ) x. %s ) <_ ( # ` P )' % NSQ)
XB = ('( ( ( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) ) /\\ ( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s ) ) /\\ '
      '( ( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ %s ) ) ) /\\ ( 2nd ` X ) <_ ( ( ( # ` P ) x. ( A + 3 ) ) + 1 ) ) )'
      % (MX, SX, SX, SX, PRD(SX), MX, MX, MX, MX, X5, NSQ))
xb = w.s([st([ann, a2le], 'jca', '( A e. NN /\\ 2 <_ A )'),
          st([nn0, n1le], 'jca', '( N e. NN0 /\\ 1 <_ N )'),
          st([x5n0, nsn, pw], '3jca', '( %s e. NN0 /\\ %s e. NN /\\ P e. Word NN0 )' % (X5, NSQ)),
          pfun, ball, veb, supA, h10], 'a5x', '( ph -> %s )' % XB)
xb1 = st([xb], 'simpld', '( ( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) ) /\\ ( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s ) )' % (MX, SX, SX, SX, PRD(SX), MX))
xb2 = st([xb], 'simprd', '( ( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ %s ) ) ) /\\ ( 2nd ` X ) <_ ( ( ( # ` P ) x. ( A + 3 ) ) + 1 ) )' % (MX, MX, MX, X5, NSQ))
xne = st([st([xb1], 'simpld', '( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (MX, SX))], 'simpld',
         '( 1st ` X ) =/= ( inr ` (/) )')
mxn0 = st([st([st([xb1], 'simpld', '( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (MX, SX))], 'simprd',
               '( %s e. NN0 /\\ %s e. Word NN0 )' % (MX, SX))], 'simpld', '%s e. NN0' % MX)
sxw = st([st([st([xb1], 'simpld', '( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (MX, SX))], 'simprd',
              '( %s e. NN0 /\\ %s e. Word NN0 )' % (MX, SX))], 'simprd', '%s e. Word NN0' % SX)
sxfun = st([st([st([xb1], 'simprd', '( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s )' % (SX, SX, PRD(SX), MX))], 'simpld',
                '( Fun `\' %s /\\ ran %s C_ ran P )' % (SX, SX))], 'simpld', 'Fun `\' %s' % SX)
sxss = st([st([st([xb1], 'simprd', '( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s )' % (SX, SX, PRD(SX), MX))], 'simpld',
               '( Fun `\' %s /\\ ran %s C_ ran P )' % (SX, SX))], 'simprd', 'ran %s C_ ran P' % SX)
sxprd = st([st([xb1], 'simprd', '( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s )' % (SX, SX, PRD(SX), MX))], 'simprd',
           '%s = %s' % (PRD(SX), MX))
xdvd = st([st([st([xb2], 'simpld', '( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ %s ) ) )' % (MX, MX, MX, X5, NSQ))], 'simpld',
               '( A || ( %s - 1 ) /\\ N < %s )' % (MX, MX))], 'simpld', 'A || ( %s - 1 )' % MX)
xlt = st([st([st([xb2], 'simpld', '( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ %s ) ) )' % (MX, MX, MX, X5, NSQ))], 'simpld',
              '( A || ( %s - 1 ) /\\ N < %s )' % (MX, MX))], 'simprd', 'N < %s' % MX)
xub = st([st([xb2], 'simpld', '( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ %s ) ) )' % (MX, MX, MX, X5, NSQ))], 'simprd',
         '%s <_ ( N x. ( %s ^ %s ) )' % (MX, X5, NSQ))
xcst = st([xb2], 'simprd', '( 2nd ` X ) <_ ( ( ( # ` P ) x. ( A + 3 ) ) + 1 )')

# ------------------------------------------------- step 5: the output
PQS = 'prod_ q e. ran %s q' % SX
rnp = st([st([sxw, sxfun], 'jca', '( %s e. Word NN0 /\\ Fun `\' %s )' % (SX, SX)), w.inst('algprodrn')], 'syl',
         '%s = %s' % (PRD(SX), PQS))
cbv = w.s([w.s([], 'cbvprodv', '%s = %s' % (PQS, PJS))], 'a1i', '( ph -> %s = %s )' % (PQS, PJS))
mjs = st([st([st([sxprd], 'eqcomd', '%s = %s' % (MX, PRD(SX))), rnp], 'eqtrd', '%s = %s' % (MX, PQS)), cbv],
         'eqtrd', '%s = %s' % (MX, PJS))
jsm = st([mjs], 'eqcomd', '%s = %s' % (PJS, MX))
sxv = st([sxw, w.inst('rnexg')], 'syl', 'ran %s e. _V' % SX)
sxsp = st([sxss, prn], 'sseqtrd', 'ran %s C_ %s' % (SX, POOL(KJ)))
sxpw = st([st([sxv, w.inst('elpwg')], 'syl', '( ran %s e. ~P %s <-> ran %s C_ %s )' % (SX, POOL(KJ), SX, POOL(KJ))),
           sxsp], 'mpbird', 'ran %s e. ~P %s' % (SX, POOL(KJ)))
mxre = st([mxn0], 'nn0red', '%s e. RR' % MX)
m1lt = st([lit('1', 'RR'), nre, mxre, n1le, xlt], 'lelttrd', '1 < %s' % MX)
mne1 = st([lit('1', 'RR'), m1lt], 'gtned', '%s =/= 1' % MX)
ANE = '( ph /\\ ran %s = (/) )' % SX
pz = w.s([w.s([], 'simpr', '( %s -> ran %s = (/) )' % (ANE, SX))], 'prodeq1d',
         '( %s -> %s = prod_ j e. (/) j )' % (ANE, PJS))
p0 = w.s([w.s([], 'prod0', 'prod_ j e. (/) j = 1')], 'a1i', '( %s -> prod_ j e. (/) j = 1 )' % ANE)
mz = w.s([w.s([mjs], 'adantr', '( %s -> %s = %s )' % (ANE, MX, PJS)), w.s([pz, p0], 'eqtrd', '( %s -> %s = 1 )' % (ANE, PJS))],
         'eqtrd', '( %s -> %s = 1 )' % (ANE, MX))
snne = st([st([mne1], 'neneqd', '-. %s = 1' % MX), mz], 'mtand', '-. ran %s = (/)' % SX)
sne = st([snne], 'neqned', 'ran %s =/= (/)' % SX)
ldvd = st([st([lmeq, xdvd], 'eqbrtrd', '%s || ( %s - 1 )' % (LQ, MX)),
           w.s([mjs], 'oveq1d', '( ph -> ( %s - 1 ) = ( %s - 1 ) )' % (MX, PJS))], 'breqtrd',
          '%s || ( %s - 1 )' % (LQ, PJS))
nlts = st([xlt, mjs], 'breqtrd', 'N < %s' % PJS)
subs = st([st([mjs, xub], 'eqbrtrrd', '%s <_ ( N x. ( %s ^ %s ) )' % (PJS, X5, NSQ)),
           w.s([w.s([st([xceq], 'eqcomd', '%s = %s' % (X5, XQ))], 'oveq1d',
                    '( ph -> ( %s ^ %s ) = ( %s ^ %s ) )' % (X5, NSQ, XQ, NSQ))], 'oveq2d',
               '( ph -> ( N x. ( %s ^ %s ) ) = ( N x. ( %s ^ %s ) ) )' % (X5, NSQ, XQ, NSQ))], 'breqtrd',
          '%s <_ ( N x. ( %s ^ %s ) )' % (PJS, XQ, NSQ))
OANT = ('( ( ran %s =/= (/) /\\ %s || ( %s - 1 ) ) /\\ ( N < %s /\\ %s <_ ( N x. ( %s ^ %s ) ) ) )'
        % (SX, LQ, PJS, PJS, PJS, XQ, NSQ))
oant = st([st([sne, ldvd], 'jca', '( ran %s =/= (/) /\\ %s || ( %s - 1 ) )' % (SX, LQ, PJS)),
           st([nlts, subs], 'jca', '( N < %s /\\ %s <_ ( N x. ( %s ^ %s ) ) )' % (PJS, PJS, XQ, NSQ))], 'jca', OANT)
outc, OUTC = a5lib.unwind(w, 'ph', h17, OUTB,
                         [('q', 'q', '~P %s' % GW, 'ran Q', rqpw), ('m', qcard),
                          ('q', 'k', 'NN', KJ, kknn), ('m', kkcopl),
                          ('q', 's', '~P %s' % POOL(KJ), 'ran %s' % SX, sxpw), ('m', oant)])
OB = ('( ( A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ ( %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) /\\ ( 1st ` ( %s Verify %s ) ) = 1o )'
      % (SX, SX, CARM(MX), MX, MX, SX))
ob = w.s([st([qfp, zn0, kknn], '3jca', '( ran Q e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ %s e. NN )' % KJ),
          kkcopl, st([sxw, sxfun], 'jca', '( %s e. Word NN0 /\\ Fun `\' %s )' % (SX, SX)), sxsp,
          st([sxprd], 'eqcomd', '%s = %s' % (MX, PRD(SX))), st([lmeq, xdvd], 'eqbrtrd', '%s || ( %s - 1 )' % (LQ, MX)),
          outc], 'a5o', '( ph -> %s )' % OB)
oprm = st([st([ob], 'simp1d', '( A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) )' % (SX, SX))], 'simpld',
          'A. b e. ran %s b e. Prime' % SX)
o3 = st([st([ob], 'simp1d', '( A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) )' % (SX, SX))], 'simprd',
        '3 <_ ( # ` %s )' % SX)
ocarm = st([st([ob], 'simp2d', '( %s /\\ %s <_ ( N ^c ( 1 + D ) ) )' % (CARM(MX), MX))], 'simpld', CARM(MX))
oub = st([st([ob], 'simp2d', '( %s /\\ %s <_ ( N ^c ( 1 + D ) ) )' % (CARM(MX), MX))], 'simprd',
         '%s <_ ( N ^c ( 1 + D ) )' % MX)
over = st([ob], 'simp3d', '( 1st ` ( %s Verify %s ) ) = 1o' % (MX, SX))
uone = st([w.s([h11], 'fveq2d', '( ph -> ( 1st ` U ) = ( 1st ` ( %s Verify %s ) ) )' % (MX, SX)), over], 'eqtrd',
          '( 1st ` U ) = 1o')

x5rr = st([x5n0], 'nn0red', '%s e. RR' % X5)
x79re = st([x5rr, st([x5n0], 'nn0ge0d', '0 <_ %s' % X5), lit('( ; 7 9 / ; ; 1 0 0 )', 'RR')], 'recxpcld',
           '( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) e. RR' % X5)
kk79 = st([st([kkn0], 'nn0red', '%s e. RR' % KJ), st([h14], 'nnred', 'K e. RR'), x79re, kkle, kx2], 'letrd',
          '%s <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) )' % (KJ, X5))
BSTEPS = [jne, kknn, kk79, jcst, pw, prn, pcard, ball, xne, mxn0, sxw, sxfun, sxss, sxprd, xlt, xcst,
          oprm, o3, ocarm, oub, uone]
_b, _BT = a5lib.conj(w, 'ph', BSTEPS[:-1], BTEXTS[:-1])
assert ' '.join(a5lib.bundletext(BTEXTS[:-1]).split()) == ' '.join(_BT.split()), _BT
w.qed([_b, uone], 'jca', '( ph -> %s )' % BUN)
run(w)


# =============================================================== a5pkb
w = WH('a5pkb', 'The operation count and the search value on the success path (Lean: SearchAlg.lean lines 216-260).')
h1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
h2 = w.h('( T e. NN0 /\\ H e. NN0 )')
h3 = w.h('N e. ( ZZ>= ` 3 )')
h4 = w.h('R = ( ( Z Reservoir W ) ` Y )')
h5 = w.h('I = ( # ` %s )' % R1)
h6 = w.h('Q = ( %s substr <. ( I - T ) , I >. )' % R1)
h7 = w.h('A = %s' % PRDQ)
h8 = w.h('J = %s' % SCN)
h9 = w.h('P = %s' % PJ)
h10 = w.h('X = ( ( A Extract N ) ` P )')
h11 = w.h('U = ( %s Verify %s )' % (MX, SX))
h12 = w.h('T <_ ( # ` %s )' % GW)
h18 = w.h(COSTB)
BH = [w.h(t) for t in BTEXTS]
(jne, kknn, kk79, jcst, pw, prn, pcard, ball, xne, mxn0, sxw, sxfun, sxss, sxprd, xlt, xcst,
 oprm, o3, ocarm, oub, uone) = BH
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
lit = lambda t, k: w.s([num.fact(w, t, k)], 'a1i', '( ph -> %s )' % (('%s e. %s' % (t, k)) if k in ('RR', 'NN0', 'NN', 'CC', 'RR+', 'ZZ') else {'ge0': '0 <_ %s' % t, 'gt0': '0 < %s' % t}[k]))
znn = st([h1], 'simp1d', 'Z e. NN')
wn0 = st([h1], 'simp2d', 'W e. NN0')
ynn = st([h1], 'simp3d', 'Y e. NN')
tn0 = st([h2], 'simpld', 'T e. NN0')
hn0 = st([h2], 'simprd', 'H e. NN0')
zn0 = st([znn], 'nnnn0d', 'Z e. NN0')
yn0 = st([ynn], 'nnnn0d', 'Y e. NN0')
nn0 = st([lit('3', 'NN0'), h3, w.inst('eluznn0')], 'syl2anc', 'N e. NN0')
nuz2 = st([h3, w.inst('uzuzle23')], 'syl', 'N e. ( ZZ>= ` 2 )')
kkn0 = st([kknn], 'nnnn0d', '%s e. NN0' % KJ)
ti = w.s([h1, h4, h5, h12], 'a5ti', '( ph -> T <_ I )')
QB = ('( ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) ) /\\ '
      '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) )' % GW)
qb = w.s([h1, tn0, h4, h5, h6, ti], 'a5q', '( ph -> %s )' % QB)
qb1 = st([qb], 'simpld', '( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) )')
qb2 = st([qb], 'simprd', '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % GW)
qwf = st([qb1], 'simpld', '( Q e. Word NN0 /\\ Fun `\' Q )')
qcl = st([qwf], 'simpld', 'Q e. Word NN0')
qfun = st([qwf], 'simprd', 'Fun `\' Q')
qlens = st([qb1], 'simprd', '( ( # ` Q ) = T /\\ ( # ` ran Q ) = T )')
qlen = st([qlens], 'simpld', '( # ` Q ) = T')
qcard = st([qlens], 'simprd', '( # ` ran Q ) = T')
qsf = st([qb2], 'simpld', '( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) )' % GW)
qfp = st([qsf], 'simprd', 'ran Q e. ( ~P Prime i^i Fin )')
qall = st([qb2], 'simprd', 'A. c e. ran Q ( c e. Prime /\\ c <_ Z )')
QA = '( ( A e. NN /\\ %s e. NN ) /\\ ( %s = A /\\ %s = %s ) /\\ A <_ ( Z ^ T ) )' % (X5, LQ, XQ, X5)
qa = w.s([qwf, st([zn0, tn0], 'jca', '( Z e. NN0 /\\ T e. NN0 )'), qlen, qall, h7], 'a5qa', '( ph -> %s )' % QA)
apair = st([qa], 'simp1d', '( A e. NN /\\ %s e. NN )' % X5)
ann = st([apair], 'simpld', 'A e. NN')
x5n0 = st([st([apair], 'simprd', '%s e. NN' % X5)], 'nnnn0d', '%s e. NN0' % X5)
an0 = st([ann], 'nnnn0d', 'A e. NN0')
azt = st([qa], 'simp3d', 'A <_ ( Z ^ T )')

# ------------------------------------------------- step 6: the cost
pcT = w.s([st([qfp, zn0, kknn], '3jca', '( ran Q e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ %s e. NN )' % KJ), qcard],
          'a5pc', '( ph -> ( # ` %s ) <_ ( 2 ^ T ) )' % POOL(KJ))
pleT = st([pcard, pcT], 'eqbrtrd', '( # ` P ) <_ ( 2 ^ T )')
sxlen = st([st([sxw, pw], 'jca', '( %s e. Word NN0 /\\ P e. Word NN0 )' % SX),
            st([sxfun, sxss], 'jca', '( Fun `\' %s /\\ ran %s C_ ran P )' % (SX, SX)), w.inst('algwrdss')], 'syl2anc',
           '( # ` %s ) <_ ( # ` P )' % SX)
sxn0 = st([sxw, w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % SX)
pn0 = st([pw, w.inst('lencl')], 'syl', '( # ` P ) e. NN0')
twn0 = st([lit('2', 'NN0'), tn0, w.inst('nn0expcl')], 'syl2anc', '( 2 ^ T ) e. NN0')
sleT = st([st([sxn0], 'nn0red', '( # ` %s ) e. RR' % SX), st([pn0], 'nn0red', '( # ` P ) e. RR'),
           st([twn0], 'nn0red', '( 2 ^ T ) e. RR'), sxlen, pleT], 'letrd', '( # ` %s ) <_ ( 2 ^ T )' % SX)
ANB2 = '( ph /\\ b e. ran %s )' % SX
b2st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (ANB2, f))
bmem2 = b2st([w.s([sxss], 'adantr', '( %s -> ran %s C_ ran P )' % (ANB2, SX)),
              w.s([], 'simpr', '( %s -> b e. ran %s )' % (ANB2, SX))], 'sseldd', 'b e. ran P')
bx2 = b2st([b2st([w.s([ball], 'adantr', '( %s -> A. b e. ran P ( 2 <_ b /\\ b <_ %s ) )' % (ANB2, X5)), bmem2,
                  w.inst('rspa')], 'syl2anc', '( 2 <_ b /\\ b <_ %s )' % X5)], 'simprd', 'b <_ %s' % X5)
ballsx = w.s([bx2], 'ralrimiva', '( ph -> A. b e. ran %s b <_ %s )' % (SX, X5))
_sc, _SC = a5lib.conj(w, 'ph', [qcl, x5n0, zn0, hn0, lit('1', 'NN0'), x5n0],
                      ['Q e. Word NN0', '%s e. NN0' % X5, 'Z e. NN0', 'H e. NN0', '1 e. NN0', '%s e. NN0' % X5])
jcl = st([_sc, w.inst('scancl')], 'syl', '%s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )' % SCN)
jc2 = st([st([h8, jcl], 'eqeltrd', 'J e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'), w.inst('xp2nd')], 'syl',
         '( 2nd ` J ) e. NN0')
xcl = st([st([st([ann, nn0], 'jca', '( A e. NN /\\ N e. NN0 )'), pw], 'jca',
             '( ( A e. NN /\\ N e. NN0 ) /\\ P e. Word NN0 )'), w.inst('extractcl')], 'syl',
         '( ( A Extract N ) ` P ) e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )')
xc2 = st([st([h10, xcl], 'eqeltrd', 'X e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'), w.inst('xp2nd')], 'syl',
         '( 2nd ` X ) e. NN0')
ucl = st([st([mxn0, sxw], 'jca', '( %s e. NN0 /\\ %s e. Word NN0 )' % (MX, SX)), w.inst('verifycl')], 'syl',
         '( %s Verify %s ) e. ( 2o X. NN0 )' % (MX, SX))
uc2 = st([st([h11, ucl], 'eqeltrd', 'U e. ( 2o X. NN0 )'), w.inst('xp2nd')], 'syl', '( 2nd ` U ) e. NN0')
cbst, _cb = w.congr(CB('( # ` Q )', KJ), {}, 'ph', {}, rules={'( # ` Q )': ('T', qlen)})
assert ' '.join(_cb.split()) == ' '.join(CB('T', KJ).split()), _cb
jcstT = st([jcst, cbst], 'breqtrd', '( 2nd ` J ) <_ %s' % CB('T', KJ))
cost = w.s([h1, st([tn0, kkn0], 'jca', '( T e. NN0 /\\ %s e. NN0 )' % KJ), h4,
            st([ann, pw, sxw], '3jca', '( A e. NN /\\ P e. Word NN0 /\\ %s e. Word NN0 )' % SX),
            jcstT, xcst, mxn0, ballsx, h11,
            st([jc2, xc2, uc2], '3jca', '( ( 2nd ` J ) e. NN0 /\\ ( 2nd ` X ) e. NN0 /\\ ( 2nd ` U ) e. NN0 )')],
           'a5cost', '( ph -> %s <_ %s )' % (COSTEX, CP))
BND = ('( ( A <_ ( Z ^ T ) /\\ %s = ( A ^ 5 ) ) /\\ ( %s <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) /\\ ( ( # ` P ) <_ ( 2 ^ T ) /\\ ( # ` %s ) <_ ( 2 ^ T ) ) ) )'
       % (X5, KJ, X5, SX))
bnd = st([st([azt, w.s([], 'eqidd', '( ph -> %s = ( A ^ 5 ) )' % X5)], 'jca',
             '( A <_ ( Z ^ T ) /\\ %s = ( A ^ 5 ) )' % X5),
          st([kk79, st([pleT, sleT], 'jca', '( ( # ` P ) <_ ( 2 ^ T ) /\\ ( # ` %s ) <_ ( 2 ^ T ) )' % SX)], 'jca',
             '( %s <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) /\\ ( ( # ` P ) <_ ( 2 ^ T ) /\\ ( # ` %s ) <_ ( 2 ^ T ) ) )' % (KJ, X5, SX))],
         'jca', BND)
cb, CBT = a5lib.unwind(w, 'ph', h18, COSTB,
                       [('q', 'l', 'NN0', 'A', an0), ('q', 'x', 'NN0', X5, x5n0),
                        ('q', 'k', 'NN0', KJ, kkn0), ('q', 'p', 'NN0', '( # ` P )', pn0),
                        ('q', 's', 'NN0', '( # ` %s )' % SX, sxn0), ('m', bnd)])
_cpc, _CPC = a5lib.conj(w, 'ph', [zn0, st([ynn], 'nnnn0d', 'Y e. NN0'), tn0, an0, x5n0, kkn0, pn0, sxn0],
                        ['Z e. NN0', 'Y e. NN0', 'T e. NN0', 'A e. NN0', '%s e. NN0' % X5,
                         '%s e. NN0' % KJ, '( # ` P ) e. NN0', '( # ` %s ) e. NN0' % SX])
cpcl = st([st([_cpc, w.inst('costpiecescl')], 'syl', '%s e. NN0' % CP)], 'nn0red', '%s e. RR' % CP)
_r1, _R1T = a5lib.conj(w, 'ph', [znn, wn0, ynn], ['Z e. NN', 'W e. NN0', 'Y e. NN'])
_resc = st([_r1, w.inst('reservoircl')], 'syl', '( ( Z Reservoir W ) ` Y ) e. ( Word NN0 X. NN0 )')
r2n0 = st([st([h4, _resc], 'eqeltrd', 'R e. ( Word NN0 X. NN0 )'), w.inst('xp2nd')], 'syl', '( 2nd ` R ) e. NN0')
from cl import Closure
_cls = Closure(w, 'ph', {'T': ('NN0', tn0)})
for _t, _s in (('( 2nd ` R )', r2n0), ('( 2nd ` J )', jc2), ('( 2nd ` X )', xc2), ('( 2nd ` U )', uc2)):
    _cls.leaf(_t, 'NN0', _s)
cexre = _cls.mem(COSTEX, 'RR')
ell2re = st([nuz2, w.inst('ell2cl')], 'syl', '( ell2 ` N ) e. RR')
ell3re = st([h3, w.inst('ell3cl')], 'syl', '( ell3 ` N ) e. RR')
expre = st([st([st([lit('; ; 1 0 0', 'RR'), ell2re], 'remulcld', '( ; ; 1 0 0 x. ( ell2 ` N ) ) e. RR'), ell3re],
            'remulcld', '( ( ; ; 1 0 0 x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) e. RR')], 'reefcld', '%s e. RR' % EXPB)
costle = st([cexre, cpcl, expre, cost, cb], 'letrd', '%s <_ %s' % (COSTEX, EXPB))

# ------------------------------------------------- step 7: the search value
plsp = st([qcl, w.inst('prodlspec')], 'syl', '( 1st ` %s ) = %s' % (PROD, PRDQ))
aeq = st([h7, st([plsp], 'eqcomd', '%s = ( 1st ` %s )' % (PRDQ, PROD))], 'eqtrd', 'A = ( 1st ` %s )' % PROD)
geq = w.s([], 'eqidd', '( ph -> %s = %s )' % (PROD, PROD))
ceq = w.s([], 'eqidd', '( ph -> %s = %s )' % (CC, CC))
ok = w.s([st([znn, wn0], 'jca', '( Z e. NN /\\ W e. NN0 )'), st([ynn, tn0], 'jca', '( Y e. NN /\\ T e. NN0 )'),
          st([hn0, nn0], 'jca', '( H e. NN0 /\\ N e. NN0 )'), h4, h5, h6, geq, aeq, ceq, h8, h9, h10, h11,
          ti, jne, xne, uone], 'srchok',
         '( ph -> %s = <. ( inl ` <. %s , %s >. ) , %s >. )' % (SR, MX, SX, CSUM))
mv = w.s([w.s([], 'fvex', '%s e. _V' % MX)], 'a1i', '( ph -> %s e. _V )' % MX)
sv = w.s([w.s([], 'fvex', '%s e. _V' % SX)], 'a1i', '( ph -> %s e. _V )' % SX)
kv = w.s([w.s([], 'ovex', '%s e. _V' % CSUM)], 'a1i', '( ph -> %s e. _V )' % CSUM)
proj = st([st([st([mv, sv, kv], '3jca', '( %s e. _V /\\ %s e. _V /\\ %s e. _V )' % (MX, SX, CSUM)), ok], 'jca',
              '( ( %s e. _V /\\ %s e. _V /\\ %s e. _V ) /\\ %s = <. ( inl ` <. %s , %s >. ) , %s >. )'
              % (MX, SX, CSUM, SR, MX, SX, CSUM)), w.inst('okproj')], 'syl',
          '( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ ( %s = %s /\\ %s = %s ) /\\ ( 2nd ` %s ) = %s )'
          % (SR, MMR, MX, SSR, SX, SR, CSUM))
srne = st([proj], 'simp1d', '( 1st ` %s ) =/= ( inr ` (/) )' % SR)
mmr = st([st([proj], 'simp2d', '( %s = %s /\\ %s = %s )' % (MMR, MX, SSR, SX))], 'simpld', '%s = %s' % (MMR, MX))
ssr = st([st([proj], 'simp2d', '( %s = %s /\\ %s = %s )' % (MMR, MX, SSR, SX))], 'simprd', '%s = %s' % (SSR, SX))
srcost = st([proj], 'simp3d', '( 2nd ` %s ) = %s' % (SR, CSUM))
plc = st([st([qcl, w.inst('prodlcost')], 'syl', '( 2nd ` %s ) = ( # ` Q )' % PROD), qlen], 'eqtrd',
         '( 2nd ` %s ) = T' % PROD)
e1 = w.s([plc], 'oveq2d', '( ph -> ( ( ( 2nd ` R ) + T ) + ( 2nd ` %s ) ) = ( ( ( 2nd ` R ) + T ) + T ) )' % PROD)
e2 = w.s([e1], 'oveq1d', '( ph -> %s = %s )' % (CC, CTT))
e3 = w.s([e2], 'oveq1d', '( ph -> ( %s + ( 2nd ` J ) ) = ( %s + ( 2nd ` J ) ) )' % (CC, CTT))
e4 = w.s([e3], 'oveq1d', '( ph -> ( ( %s + ( 2nd ` J ) ) + ( 2nd ` X ) ) = ( ( %s + ( 2nd ` J ) ) + ( 2nd ` X ) ) )' % (CC, CTT))
e5 = w.s([e4], 'oveq1d', '( ph -> %s = %s )' % (CSUM, COSTEX))
srcx = st([srcost, e5], 'eqtrd', '( 2nd ` %s ) = %s' % (SR, COSTEX))
srle = st([srcx, costle], 'eqbrtrd', '( 2nd ` %s ) <_ %s' % (SR, EXPB))

# ------------------------------------------------- step 8: the output projections
mxr = st([mmr], 'eqcomd', '%s = %s' % (MX, MMR))
sxr = st([ssr], 'eqcomd', '%s = %s' % (SX, SSR))
rfun = st([sxfun, w.s([w.s([sxr], 'cnveqd', '( ph -> `\' %s = `\' %s )' % (SX, SSR))], 'funeqd',
                      '( ph -> ( Fun `\' %s <-> Fun `\' %s ) )' % (SX, SSR))], 'mpbid', 'Fun `\' %s' % SSR)
rprm = st([oprm, w.s([w.s([sxr], 'rneqd', '( ph -> ran %s = ran %s )' % (SX, SSR))], 'raleqdv',
                     '( ph -> ( A. b e. ran %s b e. Prime <-> A. b e. ran %s b e. Prime ) )' % (SX, SSR))],
          'mpbid', 'A. b e. ran %s b e. Prime' % SSR)
r3 = st([o3, w.s([sxr], 'fveq2d', '( ph -> ( # ` %s ) = ( # ` %s ) )' % (SX, SSR))], 'breqtrd', '3 <_ ( # ` %s )' % SSR)
prdr, _pr = w.congr(PRD(SX), {}, 'ph', {}, rules={SX: (SSR, sxr)})
assert ' '.join(_pr.split()) == ' '.join(PRD(SSR).split()), _pr
rprd = st([st([mmr, st([sxprd], 'eqcomd', '%s = %s' % (MX, PRD(SX)))], 'eqtrd', '%s = %s' % (MMR, PRD(SX))), prdr],
          'eqtrd', '%s = %s' % (MMR, PRD(SSR)))
ccar, _cr = a5lib.ccongr(w, 'ph', CARM(MX), [(MX, MMR, mxr)])
assert ' '.join(_cr.split()) == ' '.join(CARM(MMR).split()), _cr
rcarm = st([ocarm, ccar], 'mpbid', CARM(MMR))
rlt = st([xlt, mxr], 'breqtrd', 'N < %s' % MMR)
rub = st([mxr, oub], 'eqbrtrrd', '%s <_ ( N ^c ( 1 + D ) )' % MMR)
w.qed([srne,
       st([st([rfun, rprm, r3], '3jca', '( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) )' % (SSR, SSR, SSR)),
           st([rprd, rcarm, st([rlt, rub], 'jca', '( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) )' % (MMR, MMR))], '3jca',
              '( %s = %s /\\ %s /\\ ( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) )' % (MMR, PRD(SSR), CARM(MMR), MMR, MMR))],
          'jca',
          '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ ( %s = %s /\\ %s /\\ ( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) ) )'
          % (SSR, SSR, SSR, MMR, PRD(SSR), CARM(MMR), MMR, MMR)),
       srle], '3jca', '( ph -> %s )' % CONCL)
run(w)

# =============================================================== a5pwk
w = WH('a5pwk', 'The search succeeds at a tuple of scales in the window, given an accepted shift of step 3 (Lean: the body of search_successW_of of SearchAlg.lean).')
g1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
g2 = w.h('( T e. NN0 /\\ H e. NN0 )')
g3 = w.h('N e. ( ZZ>= ` 3 )')
g4 = w.h('R = ( ( Z Reservoir W ) ` Y )')
g5 = w.h('I = ( # ` %s )' % R1)
g6 = w.h('Q = ( %s substr <. ( I - T ) , I >. )' % R1)
g7 = w.h('A = %s' % PRDQ)
g8 = w.h('J = %s' % SCN)
g9 = w.h('P = %s' % PJ)
g10 = w.h('X = ( ( A Extract N ) ` P )')
g11 = w.h('U = ( %s Verify %s )' % (MX, SX))
g12 = w.h('T <_ ( # ` %s )' % GW)
g13 = w.h('( %s <_ H /\\ H <_ ( ; 1 6 x. %s ) )' % (PW, PW))
g14 = w.h('K e. NN')
g15 = w.h('( ( K <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) /\\ ( K gcd %s ) = 1 ) /\\ ( ; 1 6 x. %s ) <_ ( # ` %s ) )'
          % (XQ, LQ, PW, POOL('K')))
g16 = w.h(EXTRB)
g17 = w.h(OUTB)
g18 = w.h(COSTB)
bun = w.s([g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18], 'a5pka',
          '( ph -> %s )' % BUN)
parts = a5lib.unbundle(w, 'ph', bun, BTEXTS)
w.qed([g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g18] + parts, 'a5pkb', '( ph -> %s )' % CONCL)
run(w)
