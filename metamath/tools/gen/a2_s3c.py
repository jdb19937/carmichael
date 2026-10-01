"""Sortie A2, batch 10: step3wc (the pointwise core of Step3W), step3we, step3wk
and step3w (Lean: step3_haltsW)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

FP = '( ~P Prime i^i Fin )'
FN0 = '( ~P NN0 i^i Fin )'
A2 = '( ell2 ` N )'; A3 = '( ell3 ` N )'
SQ2 = '( %s ^ 2 )' % A2
ZR = '( ( C x. %s ) x. %s )' % (A2, A3)
GPW = '( ( Z goodPrimesW W ) ` Y )'
TY = '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'
LS = '( Lmod ` S )'; XCS = '( xceil ` S )'
Q99 = '( ; 9 9 / ; ; 1 0 0 )'; Q79 = '( ; 7 9 / ; ; 2 0 0 )'; Q21 = '( ; 2 1 / ; ; 1 0 0 )'
Q79100 = '( ; 7 9 / ; ; 1 0 0 )'
C0 = '( 2 ^c ( -u D - 2 ) )'
E310 = '( exp ` ( ( 3 / ; 1 0 ) x. %s ) )' % A2
E65 = '( exp ` ( ( 6 / 5 ) x. %s ) )' % A2
KB = '( ( ; 7 5 x. ( ( abs ` G ) + 1 ) ) / %s )' % C0
WIN = '<. <. C , E >. , N >. InWindow <. <. Z , W >. , <. Y , T >. >.'
PRD = lambda l: '{ p e. Prime | p || %s }' % l
DIVL = lambda l: '{ m e. ( 1 ... %s ) | m || %s }' % (l, l)
FILT = lambda x, l: '{ d e. %s | d <_ ( %s ^c %s ) }' % (DIVL(l), x, Q21)
R2 = lambda x, l, k: '{ d e. %s | ( ( ( d x. %s ) + 1 ) <_ %s /\\ ( ( d x. %s ) + 1 ) e. Prime ) }' % (DIVL(l), k, x, k)
PIGA = lambda x, l: ('( ( %s < %s /\\ 1 < %s /\\ ( mmu ` %s ) =/= 0 ) /\\ ( A. q e. Prime ( q || %s -> q <_ ( %s ^c %s ) ) '
                     '/\\ sum_ q e. %s ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) ) )') % ('X', x, l, l, l, x, Q79, PRD(l))
PIGC = lambda x, l, k: ('( ( %s <_ ( %s ^c %s ) /\\ ( %s gcd %s ) = 1 ) /\\ ( ( %s / ( log ` %s ) ) x. ( # ` %s ) ) <_ ( # ` %s ) )'
                        % (k, x, Q79100, k, l, C0, x, FILT(x, l), R2(x, l, k)))
PIGB = lambda x, l: '( %s -> E. k e. NN %s )' % (PIGA(x, l), PIGC(x, l, 'k'))
PIG = 'A. x e. NN0 A. l e. NN0 %s' % PIGB('x', 'l')
RB = lambda v, u: 'sum_ i e. ( ( ( %s + 1 ) ... %s ) i^i Prime ) ( 1 / i ) <_ ( ( ( ( log ` %s ) - ( log ` %s ) ) + R ) / ( log ` %s ) )' % (v, u, u, v, v)
RECIP = 'A. v e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` v ) %s' % RB('v', 'u')
POOLK = lambda k: '( ( S pool Z ) ` %s )' % k
MYC = lambda k: ('( ( %s <_ ( %s ^c %s ) /\\ ( %s gcd %s ) = 1 ) /\\ ( G x. ( ( log ` N ) ^c ( 6 / 5 ) ) ) <_ ( # ` %s ) )'
                 % (k, XCS, Q79100, k, LS, POOLK(k)))

w = WH('step3wc', 'Step 3 halts at windowed scales, pointwise: some shift k coprime to L gives a large pool (Lean: the body of step3_haltsW).')
cr = w.h('C e. RR'); dr = w.h('D e. RR'); xn0 = w.h('X e. NN0'); gr = w.h('G e. RR')
rr = w.h('R e. RR'); kr = w.h('K e. RR')
c1000 = w.h('; ; ; 1 0 0 0 <_ C'); k5 = w.h('( 5 x. C ) <_ K'); kb = w.h('%s <_ K' % KB)
pig = w.h(PIG); rec = w.h(RECIP)
n3 = w.h('N e. ( ZZ>= ` 3 )'); a50 = w.h('; 5 0 <_ %s' % A2); xa = w.h('X <_ %s' % A2)
lg4c = w.h('( log ` ( 4 x. C ) ) <_ %s' % A3)
b200h = w.h('( ; ; 2 0 0 x. ( ( abs ` R ) + 2 ) ) <_ %s' % A3)
kq = w.h('( K x. %s ) <_ %s' % (SQ2, E310))
win = w.h(WIN)
sub = w.h('S C_ %s' % GPW)
hc = w.h('( # ` S ) = T')
A = 'ph'
# types and projections
ty3 = w.s([win, w.inst('inwintyp')], 'syl',
          '( %s -> ( ( C e. RR /\\ E e. RR /\\ N e. NN0 ) /\\ %s /\\ ( Y e. NN0 /\\ T e. NN0 ) ) )' % (A, '( Z e. NN0 /\\ W e. NN0 )'))
zw = w.s([ty3], 'simp2d', '( %s -> ( Z e. NN0 /\\ W e. NN0 ) )' % A)
yt = w.s([ty3], 'simp3d', '( %s -> ( Y e. NN0 /\\ T e. NN0 ) )' % A)
zn0 = w.s([zw], 'simpld', '( %s -> Z e. NN0 )' % A)
wn0 = w.s([zw], 'simprd', '( %s -> W e. NN0 )' % A)
yn0 = w.s([yt], 'simpld', '( %s -> Y e. NN0 )' % A)
tn0 = w.s([yt], 'simprd', '( %s -> T e. NN0 )' % A)
ty = w.s([zn0, wn0, yn0], '3jca', '( %s -> %s )' % (A, TY))
zlo = w.s([win, w.inst('inwinzlo')], 'syl', '( %s -> %s <_ Z )' % (A, ZR))
zhi = w.s([win, w.inst('inwinzhi')], 'syl', '( %s -> Z <_ ( 4 x. %s ) )' % (A, ZR))
wlo = w.s([win, w.inst('inwinwlo')], 'syl', '( %s -> ( Z ^c %s ) <_ ( W + 1 ) )' % (A, Q99))
tlo = w.s([win, w.inst('inwintlo')], 'syl', '( %s -> ( 3 x. %s ) <_ T )' % (A, A2))
thi = w.s([win, w.inst('inwinthi')], 'syl', '( %s -> T <_ ( 5 x. %s ) )' % (A, A2))
# reals
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
ar = w.s([n2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, A2))
br = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, A3))
absr = w.s([w.s([rr], 'recnd', '( %s -> R e. CC )' % A)], 'abscld', '( %s -> ( abs ` R ) e. RR )' % A)
absg = w.s([w.s([rr], 'recnd', '( %s -> R e. CC )' % A)], 'absge0d', '( %s -> 0 <_ ( abs ` R ) )' % A)
b200 = linarith(w, A, [b200h, absg], '; ; 2 0 0 <_ %s' % A3, leaves={A3: br, '( abs ` R )': absr})
LV = {'C': cr, A2: ar, A3: br}
a0 = linarith(w, A, [a50], '0 <_ %s' % A2, leaves=LV)
b0 = linarith(w, A, [b200], '0 < %s' % A3, leaves=LV)
bg0 = w.s([b0], 'ltled', '( %s -> 0 <_ %s )' % (A, A3))
bla = w.s([w.s([n3, w.inst('ell3lt')], 'syl', '( %s -> %s < %s )' % (A, A3, A2))], 'ltled', '( %s -> %s <_ %s )' % (A, A3, A2))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
wr = w.s([wn0], 'nn0red', '( %s -> W e. RR )' % A)
tr = w.s([tn0], 'nn0red', '( %s -> T e. RR )' % A)
# z facts
za = w.s([cr, c1000, n3, a50, b200, zn0, zlo], 's3zgea', '( %s -> %s <_ Z )' % (A, A2))
z9 = linarith(w, A, [za, a50], '9 <_ Z', leaves={A2: ar, 'Z': zr})
z0 = linarith(w, A, [za, a50], '0 < Z', leaves={A2: ar, 'Z': zr})
zq3 = w.s([w.s([zr, z9], 'jca', '( %s -> ( Z e. RR /\\ 9 <_ Z ) )' % A), w.inst('cxpge3')], 'syl',
          '( %s -> 3 <_ ( Z ^c %s ) )' % (A, Q99))
q99r = w.s([num.fact(w, Q99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, Q99))
zqr = w.s([zr, w.s([z0], 'ltled', '( %s -> 0 <_ Z )' % A), q99r], 'recxpcld', '( %s -> ( Z ^c %s ) e. RR )' % (A, Q99))
w2 = linarith(w, A, [wlo, zq3], '2 <_ W', leaves={'W': wr, '( Z ^c %s )' % Q99: zqr})
t1 = linarith(w, A, [tlo, a50], '1 <_ T', leaves={A2: ar, 'T': tr})
# S facts
sfp = w.s([w.s([ty, sub], 'jca', '( %s -> ( %s /\\ S C_ %s ) )' % (A, TY, GPW)), w.inst('s3sfp')], 'syl', '( %s -> S e. %s )' % (A, FP))
sfi = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % A)], 'simprd', '( %s -> S e. Fin )' % A)
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % A)], 'simpld', '( %s -> S C_ Prime )' % A)
hsr = w.s([w.s([sfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % A)], 'nn0red', '( %s -> ( # ` S ) e. RR )' % A)
hs1 = w.s([hc, t1], 'breqtrrd', '( %s -> 1 <_ ( # ` S ) )' % A)
hs0 = linarith(w, A, [hs1], '0 < ( # ` S )', leaves={'( # ` S )': hsr})
sne = w.s([hs0, w.s([sfi, w.inst('hashneq0')], 'syl', '( %s -> ( 0 < ( # ` S ) <-> S =/= (/) ) )' % A)], 'mpbid', '( %s -> S =/= (/) )' % A)
wlez = w.s([w.s([ty, sub, sne], '3jca', '( %s -> ( %s /\\ S C_ %s /\\ S =/= (/) ) )' % (A, TY, GPW)), w.inst('s3wlez')], 'syl',
           '( %s -> W <_ Z )' % A)
wz = w.s([wn0], 'nn0zd', '( %s -> W e. ZZ )' % A)
zz = w.s([zn0], 'nn0zd', '( %s -> Z e. ZZ )' % A)
tz2 = w.s([w.s([num.fact(w, '2', 'ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A), wz, w2], '3jca',
          '( %s -> ( 2 e. ZZ /\\ W e. ZZ /\\ 2 <_ W ) )' % A)
wuz = w.s([tz2, w.inst('eluz2')], 'sylibr', '( %s -> W e. ( ZZ>= ` 2 ) )' % A)
zuw = w.s([w.s([wz, zz, wlez], '3jca', '( %s -> ( W e. ZZ /\\ Z e. ZZ /\\ W <_ Z ) )' % A), w.inst('eluz2')], 'sylibr',
          '( %s -> Z e. ( ZZ>= ` W ) )' % A)
# logs of z
lzlb = w.s([cr, c1000, n3, a50, b200, zn0, zlo], 's3logzlb', '( %s -> %s <_ ( log ` Z ) )' % (A, A3))
lzub = w.s([cr, c1000, n3, a50, b200, zn0, zlo, lg4c, zhi], 's3logzub', '( %s -> ( log ` Z ) <_ ( 3 x. %s ) )' % (A, A3))
zrp = w.s([zr, z0], 'elrpd', '( %s -> Z e. RR+ )' % A)
lzr = w.s([zrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
lz0 = linarith(w, A, [lzlb, b200], '0 <_ ( log ` Z )', leaves={A3: br, '( log ` Z )': lzr})
p200 = w.s([w.s([num.fact(w, '; ; 2 0 0', 'RR')], 'a1i', '( %s -> ; ; 2 0 0 e. RR )' % A),
            w.s([absr, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A)], 'readdcld', '( %s -> ( ( abs ` R ) + 2 ) e. RR )' % A)], 'remulcld',
           '( %s -> ( ; ; 2 0 0 x. ( ( abs ` R ) + 2 ) ) e. RR )' % A)
b200lz = w.s([p200, br, lzr, b200h, lzlb], 'letrd', '( %s -> ( ; ; 2 0 0 x. ( ( abs ` R ) + 2 ) ) <_ ( log ` Z ) )' % A)
lw = w.s([zn0, z0, wn0, w2, wlo, zq3], 's3logw', '( %s -> ( %s x. ( log ` Z ) ) <_ ( ( log ` W ) + 1 ) )' % (A, Q99))
# the reciprocal sum
rec1 = w.s([zn0, wn0, yn0, sub, wuz, zuw, rr, rec, lw, b200lz], 's3recip', '( %s -> sum_ q e. S ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) )' % A)
rec2 = w.s([w.s([sfp, rec1], 'jca', '( %s -> ( S e. %s /\\ sum_ q e. S ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) ) )' % (A, FP)), w.inst('s3sum')], 'syl',
           '( %s -> sum_ q e. %s ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) )' % (A, PRD(LS)))
# log x
lx = w.s([n3, a0, bg0, zn0, wn0, yn0, z0, sub, hc, thi, lzub, lz0], 's3logx',
         '( %s -> ( log ` %s ) <_ ( ; 7 5 x. ( %s x. %s ) ) )' % (A, XCS, A2, A3))
lxp = w.s([sfp, hc, t1], 's3lx', '( %s -> ( 2 <_ %s /\\ 2 <_ %s ) )' % (A, LS, XCS))
l2 = w.s([lxp], 'simpld', '( %s -> 2 <_ %s )' % (A, LS))
x2 = w.s([lxp], 'simprd', '( %s -> 2 <_ %s )' % (A, XCS))
lnn = w.s([sfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (A, LS))
lr = w.s([lnn], 'nnred', '( %s -> %s e. RR )' % (A, LS))
l1gt = linarith(w, A, [l2], '1 < %s' % LS, leaves={LS: lr})
xnn = w.s([sfp, w.inst('xceilcl')], 'syl', '( %s -> %s e. NN )' % (A, XCS))
xrp = w.s([xnn], 'nnrpd', '( %s -> %s e. RR+ )' % (A, XCS))
xre = w.s([xnn], 'nnred', '( %s -> %s e. RR )' % (A, XCS))
x1gt = linarith(w, A, [x2], '1 < %s' % XCS, leaves={XCS: xre})
lx0 = w.s([x1gt, w.s([xrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < ( log ` %s ) <-> 1 < %s ) )' % (A, XCS, XCS))], 'mpbird',
          '( %s -> 0 < ( log ` %s ) )' % (A, XCS))
sqf = w.s([sfp, w.inst('prmprodsqf')], 'syl', '( %s -> ( mmu ` %s ) =/= 0 )' % (A, LS))
# z + 1 <_ exp ( ( 3 / 10 ) ell2 n )
zp1 = w.s([cr, c1000, n3, a50, b200, zn0, zhi, kr, k5, kq], 's3zp1exp', '( %s -> ( Z + 1 ) <_ %s )' % (A, E310))
e310r = w.s([w.s([w.s([num.fact(w, '( 3 / ; 1 0 )', 'RR')], 'a1i', '( %s -> ( 3 / ; 1 0 ) e. RR )' % A), ar], 'remulcld',
                 '( %s -> ( ( 3 / ; 1 0 ) x. %s ) e. RR )' % (A, A2))], 'reefcld', '( %s -> %s e. RR )' % (A, E310))
zle = linarith(w, A, [zp1], 'Z <_ %s' % E310, leaves={'Z': zr, E310: e310r})
qb = w.s([sfp, hc, zn0, wn0, yn0, sub, ar, a0, tlo, zle], 's3qb',
         '( %s -> A. q e. Prime ( q || %s -> q <_ ( %s ^c %s ) ) )' % (A, LS, XCS, Q79))
thr = w.s([sfp, hc, xn0, ar, a0, xa, tlo], 's3thr', '( %s -> X < %s )' % (A, XCS))
# apply the pigeonhole hypothesis at x = xceil Q , l = Lmod Q
xn0c = w.s([xnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (A, XCS))
ln0c = w.s([lnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (A, LS))
idx = w.s([], 'id', '( x = %s -> x = %s )' % (XCS, XCS))
cg1, _b1 = w.wcongr('A. l e. NN0 %s' % PIGB('x', 'l'), {'x': XCS}, 'x = %s' % XCS, {'x': idx})
in1 = w.s([cg1, pig, xn0c], 'rspcdva', '( %s -> A. l e. NN0 %s )' % (A, PIGB(XCS, 'l')))
idl = w.s([], 'id', '( l = %s -> l = %s )' % (LS, LS))
cg2, _b2 = w.wcongr(PIGB(XCS, 'l'), {'l': LS}, 'l = %s' % LS, {'l': idl})
in2 = w.s([cg2, in1, ln0c], 'rspcdva', '( %s -> %s )' % (A, PIGB(XCS, LS)))
ante = w.s([w.s([thr, l1gt, sqf], '3jca', '( %s -> ( X < %s /\\ 1 < %s /\\ ( mmu ` %s ) =/= 0 ) )' % (A, XCS, LS, LS)),
            w.s([qb, rec2], 'jca', '( %s -> ( A. q e. Prime ( q || %s -> q <_ ( %s ^c %s ) ) /\\ sum_ q e. %s ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) ) )' % (A, LS, XCS, Q79, PRD(LS)))], 'jca',
           '( %s -> %s )' % (A, PIGA(XCS, LS)))
exk = w.s([ante, in2], 'mpd', '( %s -> E. k e. NN %s )' % (A, PIGC(XCS, LS, 'k')))
# s3main
lxr = w.s([xrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (A, XCS))
mn = w.s([dr, gr, ar, br, a50, b0, bla, tn0, tlo, zn0, lxr, lx0, lx, zp1, kr, kb, kq], 's3main',
         '( %s -> ( ( G x. %s ) + ( Z + 1 ) ) <_ ( ( %s / ( log ` %s ) ) x. ( 2 ^ T ) ) )' % (A, E65, C0, XCS))
# pointwise upgrade under k e. NN
BB = '( %s /\\ k e. NN )' % A
knn = w.s([], 'simpr', '( %s -> k e. NN )' % BB)
CC_ = '( %s /\\ %s )' % (BB, PIGC(XCS, LS, 'k'))
pk = w.s([], 'simpr', '( %s -> %s )' % (CC_, PIGC(XCS, LS, 'k')))
pk1 = w.s([pk], 'simpld', '( %s -> ( k <_ ( %s ^c %s ) /\\ ( k gcd %s ) = 1 ) )' % (CC_, XCS, Q79100, LS))
pk2 = w.s([pk], 'simprd', '( %s -> ( ( %s / ( log ` %s ) ) x. ( # ` %s ) ) <_ ( # ` %s ) )' % (CC_, C0, XCS, FILT(XCS, LS), R2(XCS, LS, 'k')))
def up(st, f):
    return w.s([w.s([st], 'adantr', '( %s -> %s )' % (BB, f))], 'adantr', '( %s -> %s )' % (CC_, f))
u_sfp = up(sfp, 'S e. %s' % FP)
u_hc = up(hc, '( # ` S ) = T')
u_zn0 = up(zn0, 'Z e. NN0')
u_dr = up(dr, 'D e. RR')
u_lx0 = up(lx0, '0 < ( log ` %s )' % XCS)
u_knn = w.s([knn], 'adantr', '( %s -> k e. NN )' % CC_)
pool = w.s([u_sfp, u_hc, u_zn0, u_knn, u_dr, u_lx0, pk2], 's3pool',
           '( %s -> ( ( %s / ( log ` %s ) ) x. ( 2 ^ T ) ) <_ ( ( # ` %s ) + ( Z + 1 ) ) )' % (CC_, C0, XCS, POOLK('k')))
u_mn = up(mn, '( ( G x. %s ) + ( Z + 1 ) ) <_ ( ( %s / ( log ` %s ) ) x. ( 2 ^ T ) )' % (E65, C0, XCS))
# closures for the final linarith
u_gr = up(gr, 'G e. RR')
u_ar = up(ar, '%s e. RR' % A2)
u_zr = up(zr, 'Z e. RR')
e65r = w.s([w.s([w.s([num.fact(w, '( 6 / 5 )', 'RR')], 'a1i', '( %s -> ( 6 / 5 ) e. RR )' % CC_), u_ar], 'remulcld',
                '( %s -> ( ( 6 / 5 ) x. %s ) e. RR )' % (CC_, A2))], 'reefcld', '( %s -> %s e. RR )' % (CC_, E65))
ge65 = w.s([u_gr, e65r], 'remulcld', '( %s -> ( G x. %s ) e. RR )' % (CC_, E65))
pn0c = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0c], 'a1i', '( %s -> Prime C_ NN0 )' % A)], 'sstrd', '( %s -> S C_ NN0 )' % A)
u_sfn = w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % A)
sfn0 = w.s([u_sfn, w.inst('elfpw')], 'sylibr', '( %s -> S e. %s )' % (A, FN0))
u_sfn0 = up(sfn0, 'S e. %s' % FN0)
poolfi = w.s([w.s([u_sfn0, u_zn0, w.s([u_knn], 'nnnn0d', '( %s -> k e. NN0 )' % CC_)], '3jca',
                  '( %s -> ( S e. %s /\\ Z e. NN0 /\\ k e. NN0 ) )' % (CC_, FN0)), w.inst('poolfi')], 'syl',
             '( %s -> %s e. Fin )' % (CC_, POOLK('k')))
hpr = w.s([w.s([poolfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (CC_, POOLK('k')))], 'nn0red',
          '( %s -> ( # ` %s ) e. RR )' % (CC_, POOLK('k')))
cqr = w.s([w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % CC_),
                w.s([w.s([u_dr], 'renegcld', '( %s -> -u D e. RR )' % CC_), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % CC_)], 'resubcld',
                    '( %s -> ( -u D - 2 ) e. RR )' % CC_)], 'rpcxpcld', '( %s -> %s e. RR+ )' % (CC_, C0)),
           w.s([up(lxr, '( log ` %s ) e. RR' % XCS), u_lx0], 'elrpd', '( %s -> ( log ` %s ) e. RR+ )' % (CC_, XCS))], 'rpdivcld',
          '( %s -> ( %s / ( log ` %s ) ) e. RR+ )' % (CC_, C0, XCS))
cqrr = w.s([cqr], 'rpred', '( %s -> ( %s / ( log ` %s ) ) e. RR )' % (CC_, C0, XCS))
t2r = w.s([w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % CC_), up(tn0, 'T e. NN0')], 'nnexpcld',
               '( %s -> ( 2 ^ T ) e. NN )' % CC_)], 'nnred', '( %s -> ( 2 ^ T ) e. RR )' % CC_)
prod_ = w.s([cqrr, t2r], 'remulcld', '( %s -> ( ( %s / ( log ` %s ) ) x. ( 2 ^ T ) ) e. RR )' % (CC_, C0, XCS))
fin = linarith(w, CC_, [u_mn, pool], '( G x. %s ) <_ ( # ` %s )' % (E65, POOLK('k')),
               leaves={'( G x. %s )' % E65: ge65, 'Z': u_zr, '( # ` %s )' % POOLK('k'): hpr,
                       '( ( %s / ( log ` %s ) ) x. ( 2 ^ T ) )' % (C0, XCS): prod_})
ee = w.s([up(n3, 'N e. ( ZZ>= ` 3 )'), w.s([num.fact(w, '( 6 / 5 )', 'RR')], 'a1i', '( %s -> ( 6 / 5 ) e. RR )' % CC_),
          w.inst('expell2')], 'syl2anc', '( %s -> %s = ( ( log ` N ) ^c ( 6 / 5 ) ) )' % (CC_, E65))
fin2 = w.s([w.s([w.s([ee], 'oveq2d', '( %s -> ( G x. %s ) = ( G x. ( ( log ` N ) ^c ( 6 / 5 ) ) ) )' % (CC_, E65))], 'eqcomd',
                '( %s -> ( G x. ( ( log ` N ) ^c ( 6 / 5 ) ) ) = ( G x. %s ) )' % (CC_, E65)), fin], 'eqbrtrd',
           '( %s -> ( G x. ( ( log ` N ) ^c ( 6 / 5 ) ) ) <_ ( # ` %s ) )' % (CC_, POOLK('k')))
myc = w.s([pk1, fin2], 'jca', '( %s -> %s )' % (CC_, MYC('k')))
imp = w.s([myc], 'ex', '( %s -> ( %s -> %s ) )' % (BB, PIGC(XCS, LS, 'k'), MYC('k')))
rex = w.s([imp], 'reximdva', '( %s -> ( E. k e. NN %s -> E. k e. NN %s ) )' % (A, PIGC(XCS, LS, 'k'), MYC('k')))
w.qed([exk, rex], 'mpd', '( %s -> E. k e. NN %s )' % (A, MYC('k')))
run(w)

# ----------------------------------------------------------------- quadexpe
l2n = '( ell2 ` n )'; sq2n = '( %s ^ 2 )' % l2n
w = W('quadexpe', 'Eventually K ( ell2 n ) ^ 2 <_ exp ( R ell2 n ) (Lean: eventually_quad_le_exp composed with tendsto_ell2).')
PH = '( K e. RR /\\ 0 <_ K /\\ R e. RR+ )'
GOAL = '( K x. %s ) <_ ( exp ` ( R x. %s ) )' % (sq2n, l2n)
P1 = '( K x. %s ) <_ ( ( log ` n ) ^c R )' % sq2n
P2 = 'n e. ( ZZ>= ` 3 )'
q = w.s([], 'quadexp', '( %s -> %s )' % (PH, EV(P1)))
g3 = w.s([w.s([], 'evge3', EV(P2))], 'a1i', '( %s -> %s )' % (PH, EV(P2)))
both, tx = evand(w, PH, [q, g3], [P1, P2])
AA = '( %s /\\ %s )' % (PH, tx)
p1 = w.s([], 'simprl', '( %s -> %s )' % (AA, P1))
p2 = w.s([], 'simprr', '( %s -> %s )' % (AA, P2))
rr_ = w.s([w.s([], 'simpl3', '( %s -> R e. RR+ )' % AA)], 'rpred', '( %s -> R e. RR )' % AA)
ee = w.s([p2, rr_, w.inst('expell2')], 'syl2anc', '( %s -> ( exp ` ( R x. %s ) ) = ( ( log ` n ) ^c R ) )' % (AA, l2n))
pt = w.s([p1, w.s([ee], 'eqcomd', '( %s -> ( ( log ` n ) ^c R ) = ( exp ` ( R x. %s ) ) )' % (AA, l2n))], 'breqtrd',
         '( %s -> %s )' % (AA, GOAL))
w.qed([both, pt], 'evimd', '( %s -> %s )' % (PH, EV(GOAL)))
run(w)

# ------------------------------------------------------------------ step3we
l3n = '( ell3 ` n )'
F1 = 'n e. ( ZZ>= ` 3 )'
F2 = '; 5 0 <_ %s' % l2n
F3 = 'X <_ %s' % l2n
F4 = '( log ` ( 4 x. C ) ) <_ %s' % l3n
F5 = '( ; ; 2 0 0 x. ( ( abs ` R ) + 2 ) ) <_ %s' % l3n
F6 = '( K x. %s ) <_ ( exp ` ( ( 3 / ; 1 0 ) x. %s ) )' % (sq2n, l2n)
SC = '( ( ( ( ( %s /\\ %s ) /\\ %s ) /\\ %s ) /\\ %s ) /\\ %s )' % (F1, F2, F3, F4, F5, F6)

w = W('step3we', 'The scale facts Step 3 needs hold eventually (Lean: the filter_upwards list of step3_haltsW).')
PH = '( ( C e. RR /\\ 0 < C ) /\\ ( X e. NN0 /\\ R e. RR ) /\\ ( K e. RR /\\ 0 <_ K ) )'
p1c = w.s([], 'simp1', '( %s -> ( C e. RR /\\ 0 < C ) )' % PH)
cr = w.s([p1c], 'simpld', '( %s -> C e. RR )' % PH)
c0 = w.s([p1c], 'simprd', '( %s -> 0 < C )' % PH)
xn0 = w.s([w.s([], 'simp2', '( %s -> ( X e. NN0 /\\ R e. RR ) )' % PH)], 'simpld', '( %s -> X e. NN0 )' % PH)
rr = w.s([w.s([], 'simp2', '( %s -> ( X e. NN0 /\\ R e. RR ) )' % PH)], 'simprd', '( %s -> R e. RR )' % PH)
kr = w.s([w.s([], 'simp3', '( %s -> ( K e. RR /\\ 0 <_ K ) )' % PH)], 'simpld', '( %s -> K e. RR )' % PH)
k0 = w.s([w.s([], 'simp3', '( %s -> ( K e. RR /\\ 0 <_ K ) )' % PH)], 'simprd', '( %s -> 0 <_ K )' % PH)
s1 = w.s([w.s([], 'evge3', EV(F1))], 'a1i', '( %s -> %s )' % (PH, EV(F1)))
s2 = w.s([w.s([num.fact(w, '; 5 0', 'RR')], 'a1i', '( %s -> ; 5 0 e. RR )' % PH), w.inst('ell2ge')], 'syl', '( %s -> %s )' % (PH, EV(F2)))
s3 = w.s([w.s([xn0], 'nn0red', '( %s -> X e. RR )' % PH), w.inst('ell2ge')], 'syl', '( %s -> %s )' % (PH, EV(F3)))
c4rp = w.s([w.s([w.s([], '4rp', '4 e. RR+')], 'a1i', '( %s -> 4 e. RR+ )' % PH), w.s([cr, c0], 'elrpd', '( %s -> C e. RR+ )' % PH)], 'rpmulcld',
           '( %s -> ( 4 x. C ) e. RR+ )' % PH)
l4c = w.s([c4rp, w.inst('relogcl')], 'syl', '( %s -> ( log ` ( 4 x. C ) ) e. RR )' % PH)
s4 = w.s([l4c, w.inst('ell3ge')], 'syl', '( %s -> %s )' % (PH, EV(F4)))
absr = w.s([w.s([rr], 'recnd', '( %s -> R e. CC )' % PH)], 'abscld', '( %s -> ( abs ` R ) e. RR )' % PH)
p200 = w.s([w.s([num.fact(w, '; ; 2 0 0', 'RR')], 'a1i', '( %s -> ; ; 2 0 0 e. RR )' % PH),
            w.s([absr, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % PH)], 'readdcld', '( %s -> ( ( abs ` R ) + 2 ) e. RR )' % PH)], 'remulcld',
           '( %s -> ( ; ; 2 0 0 x. ( ( abs ` R ) + 2 ) ) e. RR )' % PH)
s5 = w.s([p200, w.inst('ell3ge')], 'syl', '( %s -> %s )' % (PH, EV(F5)))
r310 = w.s([num.fact(w, '( 3 / ; 1 0 )', 'RR+')], 'a1i', '( %s -> ( 3 / ; 1 0 ) e. RR+ )' % PH)
s6 = w.s([w.s([kr, k0, r310], '3jca', '( %s -> ( K e. RR /\\ 0 <_ K /\\ ( 3 / ; 1 0 ) e. RR+ ) )' % PH), w.inst('quadexpe')], 'syl',
         '( %s -> %s )' % (PH, EV(F6)))
st, tx = evand(w, PH, [s1, s2, s3, s4, s5, s6], [F1, F2, F3, F4, F5, F6])
assert tx == SC, (tx, SC)
w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
run(w)

# ------------------------------------------------------------------ step3wk
WINn = '<. <. C , E >. , n >. InWindow <. <. z , w >. , <. y , t >. >.'
GPWn = '( ( z goodPrimesW w ) ` y )'
MYCn = ('( ( k <_ ( ( xceil ` s ) ^c %s ) /\\ ( k gcd ( Lmod ` s ) ) = 1 ) /\\ ( G x. ( ( log ` n ) ^c ( 6 / 5 ) ) ) <_ ( # ` ( ( s pool z ) ` k ) ) )'
         % Q79100)
INNER = 'E. k e. NN %s' % MYCn
SQ = 'A. s e. ~P %s ( ( # ` s ) = t -> %s )' % (GPWn, INNER)
BODY = '( %s -> %s )' % (WINn, SQ)
Q4 = 'A. z e. NN0 A. w e. NN0 A. y e. NN0 A. t e. NN0 %s' % BODY

w = WH('step3wk', 'Step 3 halts at windowed scales, with the Mertens constant R and the growth constant K as parameters.')
cr = w.h('C e. RR'); dr = w.h('D e. RR'); xn0 = w.h('X e. NN0'); gr = w.h('G e. RR')
rr = w.h('R e. RR'); kr = w.h('K e. RR'); k0 = w.h('0 <_ K')
c1000 = w.h('; ; ; 1 0 0 0 <_ C'); k5 = w.h('( 5 x. C ) <_ K'); kb = w.h('%s <_ K' % KB)
pig = w.h(PIG); rec = w.h(RECIP)
A = 'ph'
c0 = linarith(w, A, [c1000], '0 < C', leaves={'C': cr})
src = w.s([w.s([w.s([cr, c0], 'jca', '( %s -> ( C e. RR /\\ 0 < C ) )' % A),
                w.s([xn0, rr], 'jca', '( %s -> ( X e. NN0 /\\ R e. RR ) )' % A),
                w.s([kr, k0], 'jca', '( %s -> ( K e. RR /\\ 0 <_ K ) )' % A)], '3jca',
               '( %s -> ( ( C e. RR /\\ 0 < C ) /\\ ( X e. NN0 /\\ R e. RR ) /\\ ( K e. RR /\\ 0 <_ K ) ) )' % A),
           w.inst('step3we')], 'syl', '( %s -> %s )' % (A, EV(SC)))
AA = '( ph /\\ %s )' % SC
ph_ = w.s([], 'simpl', '( %s -> ph )' % AA)
sc = w.s([], 'simpr', '( %s -> %s )' % (AA, SC))
l5 = w.s([sc], 'simpld', '( %s -> ( ( ( ( %s /\\ %s ) /\\ %s ) /\\ %s ) /\\ %s ) )' % (AA, F1, F2, F3, F4, F5))
f6 = w.s([sc], 'simprd', '( %s -> %s )' % (AA, F6))
l4 = w.s([l5], 'simpld', '( %s -> ( ( ( %s /\\ %s ) /\\ %s ) /\\ %s ) )' % (AA, F1, F2, F3, F4))
f5 = w.s([l5], 'simprd', '( %s -> %s )' % (AA, F5))
l3 = w.s([l4], 'simpld', '( %s -> ( ( %s /\\ %s ) /\\ %s ) )' % (AA, F1, F2, F3))
f4 = w.s([l4], 'simprd', '( %s -> %s )' % (AA, F4))
l2s = w.s([l3], 'simpld', '( %s -> ( %s /\\ %s ) )' % (AA, F1, F2))
f3 = w.s([l3], 'simprd', '( %s -> %s )' % (AA, F3))
f1 = w.s([l2s], 'simpld', '( %s -> %s )' % (AA, F1))
f2 = w.s([l2s], 'simprd', '( %s -> %s )' % (AA, F2))
BB = '( %s /\\ %s )' % (AA, WINn)
DD = '( %s /\\ s e. ~P %s )' % (BB, GPWn)
EE = '( %s /\\ ( # ` s ) = t )' % DD
def lift(st, f):
    return w.s([w.s([w.s([st], 'adantr', '( %s -> %s )' % (BB, f))], 'adantr', '( %s -> %s )' % (DD, f))], 'adantr',
               '( %s -> %s )' % (EE, f))
def liftph(st, f):
    return lift(w.s([ph_, st], 'syl', '( %s -> %s )' % (AA, f)), f)
e_cr = liftph(cr, 'C e. RR'); e_dr = liftph(dr, 'D e. RR'); e_xn0 = liftph(xn0, 'X e. NN0')
e_gr = liftph(gr, 'G e. RR'); e_rr = liftph(rr, 'R e. RR'); e_kr = liftph(kr, 'K e. RR')
e_c1000 = liftph(c1000, '; ; ; 1 0 0 0 <_ C'); e_k5 = liftph(k5, '( 5 x. C ) <_ K'); e_kb = liftph(kb, '%s <_ K' % KB)
e_pig = liftph(pig, PIG); e_rec = liftph(rec, RECIP)
e_f1 = lift(f1, F1); e_f2 = lift(f2, F2); e_f3 = lift(f3, F3); e_f4 = lift(f4, F4); e_f5 = lift(f5, F5); e_f6 = lift(f6, F6)
e_win = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (BB, WINn))], 'adantr', '( %s -> %s )' % (DD, WINn))], 'adantr',
            '( %s -> %s )' % (EE, WINn))
spw = w.s([w.s([], 'simpr', '( %s -> s e. ~P %s )' % (DD, GPWn))], 'adantr', '( %s -> s e. ~P %s )' % (EE, GPWn))
ssub = w.s([spw, w.inst('elpwi')], 'syl', '( %s -> s C_ %s )' % (EE, GPWn))
shc = w.s([], 'simpr', '( %s -> ( # ` s ) = t )' % EE)
core = w.s([e_cr, e_dr, e_xn0, e_gr, e_rr, e_kr, e_c1000, e_k5, e_kb, e_pig, e_rec,
            e_f1, e_f2, e_f3, e_f4, e_f5, e_f6, e_win, ssub, shc], 'step3wc', '( %s -> %s )' % (EE, INNER))
i1 = w.s([core], 'ex', '( %s -> ( ( # ` s ) = t -> %s ) )' % (DD, INNER))
r1 = w.s([i1], 'ralrimiva', '( %s -> %s )' % (BB, SQ))
i2 = w.s([r1], 'ex', '( %s -> %s )' % (AA, BODY))
cur = i2; body = BODY
for v in ('t', 'y', 'w', 'z'):
    ad = w.s([cur], 'adantr', '( ( %s /\\ %s e. NN0 ) -> %s )' % (AA, v, body))
    body = 'A. %s e. NN0 %s' % (v, body)
    cur = w.s([ad], 'ralrimiva', '( %s -> %s )' % (AA, body))
assert body == Q4, (body, Q4)
w.qed([src, cur], 'evimd', '( ph -> %s )' % EV(Q4))
run(w)

# ------------------------------------------------------------------ step3wr
w = WH('step3wr', 'Step 3 halts at windowed scales, with the Mertens constant R as a parameter.')
cr = w.h('C e. RR'); dr = w.h('D e. RR'); xn0 = w.h('X e. NN0'); gr = w.h('G e. RR')
rr = w.h('R e. RR'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
pig = w.h(PIG); rec = w.h(RECIP)
A = 'ph'
KK = '( ( 5 x. C ) + %s )' % KB
absr = w.s([w.s([gr], 'recnd', '( %s -> G e. CC )' % A)], 'abscld', '( %s -> ( abs ` G ) e. RR )' % A)
absg = w.s([w.s([gr], 'recnd', '( %s -> G e. CC )' % A)], 'absge0d', '( %s -> 0 <_ ( abs ` G ) )' % A)
p75 = w.s([w.s([num.fact(w, '; 7 5', 'RR')], 'a1i', '( %s -> ; 7 5 e. RR )' % A),
           w.s([absr, w.s([], '1red', '( %s -> 1 e. RR )' % A)], 'readdcld', '( %s -> ( ( abs ` G ) + 1 ) e. RR )' % A)], 'remulcld',
          '( %s -> ( ; 7 5 x. ( ( abs ` G ) + 1 ) ) e. RR )' % A)
p750 = linarith(w, A, [absg], '0 <_ ( ; 7 5 x. ( ( abs ` G ) + 1 ) )', leaves={'( abs ` G )': absr})
dneg = w.s([w.s([dr], 'renegcld', '( %s -> -u D e. RR )' % A), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A)], 'resubcld',
           '( %s -> ( -u D - 2 ) e. RR )' % A)
c0rp = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A), dneg], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, C0))
kbr = w.s([p75, c0rp], 'rerpdivcld', '( %s -> %s e. RR )' % (A, KB))
kb0 = w.s([p75, c0rp, p750], 'divge0d', '( %s -> 0 <_ %s )' % (A, KB))
f5c = w.s([w.s([num.fact(w, '5', 'RR')], 'a1i', '( %s -> 5 e. RR )' % A), cr], 'remulcld', '( %s -> ( 5 x. C ) e. RR )' % A)
kkr = w.s([f5c, kbr], 'readdcld', '( %s -> %s e. RR )' % (A, KK))
LVK = {'C': cr, KB: kbr}
kk0 = linarith(w, A, [c1000, kb0], '0 <_ %s' % KK, leaves=LVK)
kk5 = linarith(w, A, [kb0], '( 5 x. C ) <_ %s' % KK, leaves=LVK)
kkb = linarith(w, A, [c1000], '%s <_ %s' % (KB, KK), leaves=LVK)
w.qed([cr, dr, xn0, gr, rr, kkr, kk0, c1000, kk5, kkb, pig, rec], 'step3wk', '( %s -> %s )' % (A, EV(Q4)))
run(w)

# ------------------------------------------------------------------- step3w
SM = lambda p, wv, zu: 'sum_ %s e. ( ( ( %s + 1 ) ... %s ) i^i Prime ) ( 1 / %s )' % (p, wv, zu, p)
RH = lambda c, wv, zu: '( ( ( ( log ` %s ) - ( log ` %s ) ) + %s ) / ( log ` %s ) )' % (zu, wv, c, wv)
BD = lambda p, c, wv, zu: '%s <_ %s' % (SM(p, wv, zu), RH(c, wv, zu))
IN2 = lambda p, c, wv: 'A. %s e. ( ZZ>= ` %s ) %s' % ('z' if p == 'p' and wv == 'w' else 'u', wv, BD(p, c, wv, 'z' if p == 'p' and wv == 'w' else 'u'))

w = WH('step3w', 'Lemma 4.2 (Step 3 halts) at windowed scales: for n large, any scales in the window and any admissible Q of size T , some shift k coprime to L yields a pool of at least c ( log n ) ^ 1.2 primes (Lean: step3_haltsW of Step3W.lean).')
cr = w.h('C e. RR'); dr = w.h('D e. RR'); er = w.h('E e. RR'); xn0 = w.h('X e. NN0'); gr = w.h('G e. RR')
e0 = w.h('0 < E'); eh = w.h('E <_ ( 1 / 2 )'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
pig = w.h(PIG)
A = 'ph'
RECr = lambda c: 'A. v e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` v ) %s' % BD('i', c, 'v', 'u')
PHI = '( ph /\\ r e. RR /\\ %s )' % RECr('r')
p1 = w.s([], 'simp1', '( %s -> ph )' % PHI)
p2 = w.s([], 'simp2', '( %s -> r e. RR )' % PHI)
p3 = w.s([], 'simp3', '( %s -> %s )' % (PHI, RECr('r')))
def lift(st, f):
    return w.s([p1, st], 'syl', '( %s -> %s )' % (PHI, f))
inner = w.s([lift(cr, 'C e. RR'), lift(dr, 'D e. RR'), lift(xn0, 'X e. NN0'), lift(gr, 'G e. RR'),
             p2, lift(c1000, '; ; ; 1 0 0 0 <_ C'), lift(pig, PIG), p3], 'step3wr', '( %s -> %s )' % (PHI, EV(Q4)))
ex = w.s([inner], '3expia', '( ( ph /\\ r e. RR ) -> ( %s -> %s ) )' % (RECr('r'), EV(Q4)))
rl = w.s([ex], 'rexlimdva', '( ph -> ( E. r e. RR %s -> %s ) )' % (RECr('r'), EV(Q4)))
# rename the bound variables of recipsum: p -> i , z -> u , w -> v , c -> r
src = w.s([], 'recipsum', 'E. c e. RR A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s' % BD('p', 'c', 'w', 'z'))
cbs = w.s([w.s([], 'oveq2', '( p = i -> ( 1 / p ) = ( 1 / i ) )')], 'cbvsumv', '%s = %s' % (SM('p', 'w', 'z'), SM('i', 'w', 'z')))
b1 = w.s([cbs], 'breq1i', '( %s <-> %s )' % (BD('p', 'c', 'w', 'z'), BD('i', 'c', 'w', 'z')))
b1a = w.s([b1], 'ralbii', '( A. z e. ( ZZ>= ` w ) %s <-> A. z e. ( ZZ>= ` w ) %s )' % (BD('p', 'c', 'w', 'z'), BD('i', 'c', 'w', 'z')))
b1b = w.s([b1a], 'ralbii', '( A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s <-> A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s )' % (BD('p', 'c', 'w', 'z'), BD('i', 'c', 'w', 'z')))
b1c = w.s([b1b], 'rexbii', '( E. c e. RR A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s <-> E. c e. RR A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s )' % (BD('p', 'c', 'w', 'z'), BD('i', 'c', 'w', 'z')))
s1 = w.s([src, b1c], 'mpbi', 'E. c e. RR A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s' % BD('i', 'c', 'w', 'z'))
idz = w.s([], 'id', '( z = u -> z = u )')
cg1, _b = w.wcongr(BD('i', 'c', 'w', 'z'), {'z': 'u'}, 'z = u', {'z': idz})
b2 = w.s([cg1], 'cbvralvw', '( A. z e. ( ZZ>= ` w ) %s <-> A. u e. ( ZZ>= ` w ) %s )' % (BD('i', 'c', 'w', 'z'), BD('i', 'c', 'w', 'u')))
b2a = w.s([b2], 'ralbii', '( A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s <-> A. w e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` w ) %s )' % (BD('i', 'c', 'w', 'z'), BD('i', 'c', 'w', 'u')))
b2b = w.s([b2a], 'rexbii', '( E. c e. RR A. w e. ( ZZ>= ` 2 ) A. z e. ( ZZ>= ` w ) %s <-> E. c e. RR A. w e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` w ) %s )' % (BD('i', 'c', 'w', 'z'), BD('i', 'c', 'w', 'u')))
s2 = w.s([s1, b2b], 'mpbi', 'E. c e. RR A. w e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` w ) %s' % BD('i', 'c', 'w', 'u'))
idw = w.s([], 'id', '( w = v -> w = v )')
cg2, _b2 = w.wcongr('A. u e. ( ZZ>= ` w ) %s' % BD('i', 'c', 'w', 'u'), {'w': 'v'}, 'w = v', {'w': idw})
b3 = w.s([cg2], 'cbvralvw', '( A. w e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` w ) %s <-> A. v e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` v ) %s )' % (BD('i', 'c', 'w', 'u'), BD('i', 'c', 'v', 'u')))
b3a = w.s([b3], 'rexbii', '( E. c e. RR A. w e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` w ) %s <-> E. c e. RR %s )' % (BD('i', 'c', 'w', 'u'), RECr('c')))
s3 = w.s([s2, b3a], 'mpbi', 'E. c e. RR %s' % RECr('c'))
idc = w.s([], 'id', '( c = r -> c = r )')
cg3, _b3 = w.wcongr(RECr('c'), {'c': 'r'}, 'c = r', {'c': idc})
b4 = w.s([cg3], 'cbvrexvw', '( E. c e. RR %s <-> E. r e. RR %s )' % (RECr('c'), RECr('r')))
s4 = w.s([s3, b4], 'mpbi', 'E. r e. RR %s' % RECr('r'))
s5 = w.s([s4], 'a1i', '( ph -> E. r e. RR %s )' % RECr('r'))
w.qed([s5, rl], 'mpd', '( ph -> %s )' % EV(Q4))
run(w)
