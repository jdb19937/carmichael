"""Sortie A2, batch 4: the counting step of Step2W (the AGP smooth-shifted set
sits in the reservoir together with the primes below the floor)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

L2 = '( ell2 ` N )'; L3 = '( ell3 ` N )'
XE = '( Z ^c ( 1 - E ) )'
SMQ = lambda x, B: 'A. q e. Prime ( q || ( %s - 1 ) -> q <_ %s )' % (x, B)
SMP = lambda x, B: 'A. p e. Prime ( p || ( %s - 1 ) -> p <_ %s )' % (x, B)
COND = lambda x, B: '( %s e. Prime /\\ %s )' % (x, SMQ(x, B))
SS = '{ a e. ( 0 ... Z ) | %s }' % COND('a', XE)
GPW = '( ( Z goodPrimesW W ) ` Y )'

# ------------------------------------------------------------------ s2sub
w = WH('s2sub', 'The AGP smooth-shifted primes up to z lie in the windowed reservoir together with the integers up to the floor w (Lean: Step2W.lean hsub).')
zn0 = w.h('Z e. NN0'); wn0 = w.h('W e. NN0'); yn0 = w.h('Y e. NN0')
er = w.h('E e. RR'); xey = w.h('%s <_ Y' % XE)
A = '( ph /\\ r e. %s )' % SS
# membership in SS
idr = w.s([], 'id', '( a = r -> a = r )')
cg, _b = w.wcongr(COND('a', XE), {'a': 'r'}, 'a = r', {'a': idr})
elr = w.s([cg], 'elrab', '( r e. %s <-> ( r e. ( 0 ... Z ) /\\ %s ) )' % (SS, COND('r', XE)))
rin = w.s([], 'simpr', '( %s -> r e. %s )' % (A, SS))
rb = w.s([rin, w.s([elr], 'a1i', '( %s -> ( r e. %s <-> ( r e. ( 0 ... Z ) /\\ %s ) ) )' % (A, SS, COND('r', XE)))], 'mpbid',
         '( %s -> ( r e. ( 0 ... Z ) /\\ %s ) )' % (A, COND('r', XE)))
rfz = w.s([rb], 'simpld', '( %s -> r e. ( 0 ... Z ) )' % A)
rc = w.s([rb], 'simprd', '( %s -> %s )' % (A, COND('r', XE)))
rp = w.s([rc], 'simpld', '( %s -> r e. Prime )' % A)
rsm = w.s([rc], 'simprd', '( %s -> %s )' % (A, SMQ('r', XE)))
# rename the bound variable of the smoothness conjunct and weaken the bound
idq = w.s([], 'id', '( q = p -> q = p )')
cb, _b2 = w.wcongr('( q || ( r - 1 ) -> q <_ %s )' % XE, {'q': 'p'}, 'q = p', {'q': idq})
cbv = w.s([cb], 'cbvralvw', '( %s <-> %s )' % (SMQ('r', XE), SMP('r', XE)))
rsmp = w.s([rsm, w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, SMQ('r', XE), SMP('r', XE)))], 'mpbid',
           '( %s -> %s )' % (A, SMP('r', XE)))
B = '( %s /\\ p e. Prime )' % A
pr = w.s([], 'simpr', '( %s -> p e. Prime )' % B)
prr = w.s([pr, w.inst('prmnn')], 'syl', '( %s -> p e. NN )' % B)
prre = w.s([prr], 'nnred', '( %s -> p e. RR )' % B)
zn0b = w.s([w.s([], 'simpl', '( %s -> ph )' % A)], 'adantr', '( %s -> ph )' % B)
zr = w.s([zn0], 'nn0red', '( ph -> Z e. RR )')
zge = w.s([zn0], 'nn0ge0d', '( ph -> 0 <_ Z )')
oe = w.s([], '1red', '( ph -> 1 e. RR )')
esub = w.s([oe, er], 'resubcld', '( ph -> ( 1 - E ) e. RR )')
xer = w.s([zr, zge, esub], 'recxpcld', '( ph -> %s e. RR )' % XE)
yr = w.s([yn0], 'nn0red', '( ph -> Y e. RR )')
xerb = w.s([xer], 'ad2antrr', '( %s -> %s e. RR )' % (B, XE))
yrb = w.s([yr], 'ad2antrr', '( %s -> Y e. RR )' % B)
xeyb = w.s([xey], 'ad2antrr', '( %s -> %s <_ Y )' % (B, XE))
rsmb = w.s([rsmp], 'adantr', '( %s -> %s )' % (B, SMP('r', XE)))
inst = w.s([rsmb, pr, w.inst('rspa')], 'syl2anc', '( %s -> ( p || ( r - 1 ) -> p <_ %s ) )' % (B, XE))
C = '( %s /\\ p || ( r - 1 ) )' % B
instc = w.s([inst], 'imp', '( %s -> p <_ %s )' % (C, XE))
le2 = w.s([w.s([prre], 'adantr', '( %s -> p e. RR )' % C), w.s([xerb], 'adantr', '( %s -> %s e. RR )' % (C, XE)),
           w.s([yrb], 'adantr', '( %s -> Y e. RR )' % C), instc, w.s([xeyb], 'adantr', '( %s -> %s <_ Y )' % (C, XE))],
          'letrd', '( %s -> p <_ Y )' % C)
imp2 = w.s([le2], 'ex', '( %s -> ( p || ( r - 1 ) -> p <_ Y ) )' % B)
ral2 = w.s([imp2], 'ralrimiva', '( %s -> %s )' % (A, SMP('r', 'Y')))
# case w < r
D = '( %s /\\ W < r )' % A
big = w.s([], 'simpr', '( %s -> W < r )' % D)
gb = w.s([zn0, wn0, yn0], '3jca', '( ph -> ( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 ) )')
gbi = w.s([gb, w.inst('elgoodprimesw')], 'syl',
          '( ph -> ( r e. %s <-> ( r e. ( 0 ... Z ) /\\ ( r e. Prime /\\ W < r /\\ %s ) ) ) )' % (GPW, SMP('r', 'Y')))
gbid = w.s([gbi], 'ad2antrr', '( %s -> ( r e. %s <-> ( r e. ( 0 ... Z ) /\\ ( r e. Prime /\\ W < r /\\ %s ) ) ) )' % (D, GPW, SMP('r', 'Y')))
cj = w.s([w.s([rp], 'adantr', '( %s -> r e. Prime )' % D), big, w.s([ral2], 'adantr', '( %s -> %s )' % (D, SMP('r', 'Y')))],
         '3jca', '( %s -> ( r e. Prime /\\ W < r /\\ %s ) )' % (D, SMP('r', 'Y')))
cj2 = w.s([w.s([rfz], 'adantr', '( %s -> r e. ( 0 ... Z ) )' % D), cj], 'jca',
          '( %s -> ( r e. ( 0 ... Z ) /\\ ( r e. Prime /\\ W < r /\\ %s ) ) )' % (D, SMP('r', 'Y')))
ing = w.s([cj2, gbid], 'mpbird', '( %s -> r e. %s )' % (D, GPW))
u1 = w.s([ing, w.inst('elun1')], 'syl', '( %s -> r e. ( %s u. ( 0 ... W ) ) )' % (D, GPW))
# case r <_ w
F = '( %s /\\ -. W < r )' % A
nb = w.s([], 'simpr', '( %s -> -. W < r )' % F)
rz = w.s([rfz, w.inst('elfzelz')], 'syl', '( %s -> r e. ZZ )' % A)
rzf = w.s([rz], 'adantr', '( %s -> r e. ZZ )' % F)
rre = w.s([rzf], 'zred', '( %s -> r e. RR )' % F)
wre = w.s([w.s([wn0], 'nn0red', '( ph -> W e. RR )')], 'ad2antrr', '( %s -> W e. RR )' % F)
nlt = w.s([rre, wre, w.inst('lenlt')], 'syl2anc', '( %s -> ( r <_ W <-> -. W < r ) )' % F)
rlew = w.s([nb, nlt], 'mpbir' + 'd', '( %s -> r <_ W )' % F)
r0 = w.s([w.s([rfz], 'adantr', '( %s -> r e. ( 0 ... Z ) )' % F), w.inst('elfzle1')], 'syl', '( %s -> 0 <_ r )' % F)
z0z = w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % F)
wz = w.s([w.s([wn0], 'nn0zd', '( ph -> W e. ZZ )')], 'ad2antrr', '( %s -> W e. ZZ )' % F)
j3 = w.s([z0z, wz, rzf], '3jca', '( %s -> ( 0 e. ZZ /\\ W e. ZZ /\\ r e. ZZ ) )' % F)
j4 = w.s([r0, rlew], 'jca', '( %s -> ( 0 <_ r /\\ r <_ W ) )' % F)
j5 = w.s([j3, j4], 'jca', '( %s -> ( ( 0 e. ZZ /\\ W e. ZZ /\\ r e. ZZ ) /\\ ( 0 <_ r /\\ r <_ W ) ) )' % F)
infz = w.s([j5, w.inst('elfz2')], 'sylibr', '( %s -> r e. ( 0 ... W ) )' % F)
u2 = w.s([infz, w.inst('elun2')], 'syl', '( %s -> r e. ( %s u. ( 0 ... W ) ) )' % (F, GPW))
cs = w.s([u1, u2], 'pm2.61dan', '( %s -> r e. ( %s u. ( 0 ... W ) ) )' % (A, GPW))
csx = w.s([cs], 'ex', '( ph -> ( r e. %s -> r e. ( %s u. ( 0 ... W ) ) ) )' % (SS, GPW))
w.qed([csx], 'ssrdv', '( ph -> %s C_ ( %s u. ( 0 ... W ) ) )' % (SS, GPW))
run(w)

# ------------------------------------------------------------------ s2card
SSX = lambda x: '{ a e. ( 0 ... %s ) | ( a e. Prime /\\ A. q e. Prime ( q || ( a - 1 ) -> q <_ ( %s ^c ( 1 - E ) ) ) ) }' % (x, x)
SMOOTH = 'A. x e. ( ZZ>= ` X ) ( G x. ( ppi ` x ) ) <_ ( # ` %s )' % SSX('x')
UN = '( %s u. ( 0 ... W ) )' % GPW

w = WH('s2card', 'The AGP count at z is at most the reservoir size plus the number of integers up to the floor w (Lean: Step2W.lean hcard, hkey).')
zn0 = w.h('Z e. NN0'); wn0 = w.h('W e. NN0'); yn0 = w.h('Y e. NN0')
er = w.h('E e. RR'); gr = w.h('G e. RR'); xey = w.h('%s <_ Y' % XE)
xn0 = w.h('X e. NN0'); xlez = w.h('X <_ Z'); sm = w.h(SMOOTH)
A = 'ph'
xz = w.s([xn0], 'nn0zd', '( %s -> X e. ZZ )' % A)
zz = w.s([zn0], 'nn0zd', '( %s -> Z e. ZZ )' % A)
zj = w.s([xz, zz, xlez], '3jca', '( %s -> ( X e. ZZ /\\ Z e. ZZ /\\ X <_ Z ) )' % A)
zuz = w.s([zj, w.inst('eluz2')], 'sylibr', '( %s -> Z e. ( ZZ>= ` X ) )' % A)
idx = w.s([], 'id', '( x = Z -> x = Z )')
cg, _b = w.wcongr('( G x. ( ppi ` x ) ) <_ ( # ` %s )' % SSX('x'), {'x': 'Z'}, 'x = Z', {'x': idx})
ins = w.s([cg, sm, zuz], 'rspcdva', '( %s -> ( G x. ( ppi ` Z ) ) <_ ( # ` %s ) )' % (A, SS))
sub = w.s([zn0, wn0, yn0, er, xey], 's2sub', '( %s -> %s C_ %s )' % (A, SS, UN))
# finiteness
gfi = w.s([w.s([zn0, wn0, yn0], '3jca', '( %s -> ( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 ) )' % A), w.inst('goodprimeswfi')], 'syl',
          '( %s -> %s e. ( ~P Prime i^i Fin ) )' % (A, GPW))
gfi2 = w.s([w.s([gfi, w.inst('elfpw')], 'sylib', '( %s -> ( %s C_ Prime /\\ %s e. Fin ) )' % (A, GPW, GPW))], 'simprd',
           '( %s -> %s e. Fin )' % (A, GPW))
fzfi = w.s([w.s([], 'fzfi', '( 0 ... W ) e. Fin')], 'a1i', '( %s -> ( 0 ... W ) e. Fin )' % A)
unfi = w.s([gfi2, fzfi, w.inst('unfi')], 'syl2anc', '( %s -> %s e. Fin )' % (A, UN))
hs = w.s([unfi, sub, w.inst('hashss')], 'syl2anc', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (A, SS, UN))
hu = w.s([gfi2, fzfi, w.inst('hashun2')], 'syl2anc', '( %s -> ( # ` %s ) <_ ( ( # ` %s ) + ( # ` ( 0 ... W ) ) ) )' % (A, UN, GPW))
hf = w.s([wn0, w.inst('hashfz0')], 'syl', '( %s -> ( # ` ( 0 ... W ) ) = ( W + 1 ) )' % A)
hu2 = w.s([hu, w.s([hf], 'oveq2d', '( %s -> ( ( # ` %s ) + ( # ` ( 0 ... W ) ) ) = ( ( # ` %s ) + ( W + 1 ) ) )' % (A, GPW, GPW))], 'breqtrd',
          '( %s -> ( # ` %s ) <_ ( ( # ` %s ) + ( W + 1 ) ) )' % (A, UN, GPW))
ssfi = w.s([w.s([], 'fzfi', '( 0 ... Z ) e. Fin'), w.inst('rabfi')], 'ax-mp', '%s e. Fin' % SS)
hsr = w.s([w.s([ssfi, w.inst('hashcl')], 'ax-mp', '( # ` %s ) e. NN0' % SS)], 'a1i', '( %s -> ( # ` %s ) e. NN0 )' % (A, SS))
hsre = w.s([hsr], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (A, SS))
hur = w.s([w.s([unfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A, UN))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (A, UN))
hgr = w.s([w.s([gfi2, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A, GPW))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (A, GPW))
wr = w.s([wn0], 'nn0red', '( %s -> W e. RR )' % A)
one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
sumr = w.s([hgr, w.s([wr, one], 'readdcld', '( %s -> ( W + 1 ) e. RR )' % A)], 'readdcld',
           '( %s -> ( ( # ` %s ) + ( W + 1 ) ) e. RR )' % (A, GPW))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
ppr = w.s([w.s([zr, w.inst('ppicl')], 'syl', '( %s -> ( ppi ` Z ) e. NN0 )' % A)], 'nn0red', '( %s -> ( ppi ` Z ) e. RR )' % A)
gpr = w.s([gr, ppr], 'remulcld', '( %s -> ( G x. ( ppi ` Z ) ) e. RR )' % A)
t1 = w.s([hsre, hur, sumr, hs, hu2], 'letrd', '( %s -> ( # ` %s ) <_ ( ( # ` %s ) + ( W + 1 ) ) )' % (A, SS, GPW))
w.qed([gpr, hsre, sumr, ins, t1], 'letrd', '( %s -> ( G x. ( ppi ` Z ) ) <_ ( ( # ` %s ) + ( W + 1 ) ) )' % (A, GPW))
run(w)

# ------------------------------------------------------------------ s2cheb
CHEB = 'A. u e. ( ZZ>= ` K ) ( u / ( 3 x. ( log ` u ) ) ) <_ ( ppi ` u )'
PP = '( ppi ` Z )'
w = WH('s2cheb', 'Chebyshev at the windowed scale: 10 A <_ G ppi ( z ) when 60 <_ C G, C A B <_ z and log z <_ 2 B (Lean: Step2W.lean hcheb3, hpi10).')
cr = w.h('C e. RR'); gr = w.h('G e. RR'); ar = w.h('A e. RR'); br = w.h('B e. RR')
g0 = w.h('0 < G'); c60 = w.h('; 6 0 <_ ( C x. G )')
a0 = w.h('0 <_ A'); b0 = w.h('0 < B')
zn = w.h('Z e. NN'); z1 = w.h('1 < Z')
zlo = w.h('( ( C x. A ) x. B ) <_ Z'); lz = w.h('( log ` Z ) <_ ( 2 x. B )')
kn = w.h('K e. NN'); klez = w.h('K <_ Z'); ch = w.h(CHEB)
A = 'ph'
kz = w.s([kn], 'nnzd', '( %s -> K e. ZZ )' % A)
zz = w.s([zn], 'nnzd', '( %s -> Z e. ZZ )' % A)
zuz = w.s([w.s([kz, zz, klez], '3jca', '( %s -> ( K e. ZZ /\\ Z e. ZZ /\\ K <_ Z ) )' % A), w.inst('eluz2')], 'sylibr',
          '( %s -> Z e. ( ZZ>= ` K ) )' % A)
idu = w.s([], 'id', '( u = Z -> u = Z )')
cg, _b = w.wcongr('( u / ( 3 x. ( log ` u ) ) ) <_ ( ppi ` u )', {'u': 'Z'}, 'u = Z', {'u': idu})
ins = w.s([cg, ch, zuz], 'rspcdva', '( %s -> ( Z / ( 3 x. ( log ` Z ) ) ) <_ %s )' % (A, PP))
zrp = w.s([zn], 'nnrpd', '( %s -> Z e. RR+ )' % A)
zr = w.s([zn], 'nnred', '( %s -> Z e. RR )' % A)
lzr = w.s([zrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
lzp = w.s([z1, w.s([zrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < ( log ` Z ) <-> 1 < Z ) )' % A)], 'mpbird',
          '( %s -> 0 < ( log ` Z ) )' % A)
r3 = w.s([], '3red', '( %s -> 3 e. RR )' % A) if False else w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % A)
t3 = w.s([r3, lzr], 'remulcld', '( %s -> ( 3 x. ( log ` Z ) ) e. RR )' % A)
t3p = linarith(w, A, [lzp], '0 < ( 3 x. ( log ` Z ) )', leaves={'( log ` Z )': lzr})
t3rp = w.s([t3, t3p], 'elrpd', '( %s -> ( 3 x. ( log ` Z ) ) e. RR+ )' % A)
ppn0 = w.s([zr, w.inst('ppicl')], 'syl', '( %s -> %s e. NN0 )' % (A, PP))
ppr = w.s([ppn0], 'nn0red', '( %s -> %s e. RR )' % (A, PP))
pp0 = w.s([ppn0], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A, PP))
bi = w.s([zr, ppr, t3rp], 'ledivmuld',
         '( %s -> ( ( Z / ( 3 x. ( log ` Z ) ) ) <_ %s <-> Z <_ ( ( 3 x. ( log ` Z ) ) x. %s ) ) )' % (A, PP, PP))
zle = w.s([ins, bi], 'mpbid', '( %s -> Z <_ ( ( 3 x. ( log ` Z ) ) x. %s ) )' % (A, PP))
lb = linarith(w, A, [lz], '( 3 x. ( log ` Z ) ) <_ ( 6 x. B )', leaves={'( log ` Z )': lzr, 'B': br})
sixb = w.s([w.s([w.s([], '6re', '6 e. RR')], 'a1i', '( %s -> 6 e. RR )' % A), br], 'remulcld', '( %s -> ( 6 x. B ) e. RR )' % A)
m1 = w.s([t3, sixb, ppr, pp0, lb], 'lemul1ad', '( %s -> ( ( 3 x. ( log ` Z ) ) x. %s ) <_ ( ( 6 x. B ) x. %s ) )' % (A, PP, PP))
p1 = w.s([t3, ppr], 'remulcld', '( %s -> ( ( 3 x. ( log ` Z ) ) x. %s ) e. RR )' % (A, PP))
p2 = w.s([sixb, ppr], 'remulcld', '( %s -> ( ( 6 x. B ) x. %s ) e. RR )' % (A, PP))
zle2 = w.s([zr, p1, p2, zle, m1], 'letrd', '( %s -> Z <_ ( ( 6 x. B ) x. %s ) )' % (A, PP))
cab = w.s([w.s([cr, ar], 'remulcld', '( %s -> ( C x. A ) e. RR )' % A), br], 'remulcld', '( %s -> ( ( C x. A ) x. B ) e. RR )' % A)
cab2 = w.s([cab, zr, p2, zlo, zle2], 'letrd', '( %s -> ( ( C x. A ) x. B ) <_ ( ( 6 x. B ) x. %s ) )' % (A, PP))
r6c = w.s([], '6cn', '6 e. CC'); r6cd = w.s([r6c], 'a1i', '( %s -> 6 e. CC )' % A)
bc = w.s([br], 'recnd', '( %s -> B e. CC )' % A)
ppc = w.s([ppr], 'recnd', '( %s -> %s e. CC )' % (A, PP))
m32 = w.s([r6cd, bc, ppc], 'mul32d', '( %s -> ( ( 6 x. B ) x. %s ) = ( ( 6 x. %s ) x. B ) )' % (A, PP, PP))
cab3 = w.s([cab2, m32], 'breqtrd', '( %s -> ( ( C x. A ) x. B ) <_ ( ( 6 x. %s ) x. B ) )' % (A, PP))
brp = w.s([br, b0], 'elrpd', '( %s -> B e. RR+ )' % A)
sixpp = w.s([w.s([w.s([], '6re', '6 e. RR')], 'a1i', '( %s -> 6 e. RR )' % A), ppr], 'remulcld', '( %s -> ( 6 x. %s ) e. RR )' % (A, PP))
canc = w.s([w.s([cr, ar], 'remulcld', '( %s -> ( C x. A ) e. RR )' % A), sixpp, brp], 'lemul1d',
           '( %s -> ( ( C x. A ) <_ ( 6 x. %s ) <-> ( ( C x. A ) x. B ) <_ ( ( 6 x. %s ) x. B ) ) )' % (A, PP, PP))
ca = w.s([cab3, canc], 'mpbird', '( %s -> ( C x. A ) <_ ( 6 x. %s ) )' % (A, PP))
cgr = w.s([cr, gr], 'remulcld', '( %s -> ( C x. G ) e. RR )' % A)
r60 = w.s([num.fact(w, '; 6 0', 'RR')], 'a1i', '( %s -> ; 6 0 e. RR )' % A)
m2 = w.s([r60, cgr, ar, a0, c60], 'lemul1ad', '( %s -> ( ; 6 0 x. A ) <_ ( ( C x. G ) x. A ) )' % A)
cc_ = w.s([cr], 'recnd', '( %s -> C e. CC )' % A)
gc = w.s([gr], 'recnd', '( %s -> G e. CC )' % A)
ac = w.s([ar], 'recnd', '( %s -> A e. CC )' % A)
e1 = w.s([cc_, gc, ac], 'mul32d', '( %s -> ( ( C x. G ) x. A ) = ( ( C x. A ) x. G ) )' % A)
e2 = w.s([w.s([cc_, ac], 'mulcld', '( %s -> ( C x. A ) e. CC )' % A), gc], 'mulcomd', '( %s -> ( ( C x. A ) x. G ) = ( G x. ( C x. A ) ) )' % A)
e3 = w.s([e1, e2], 'eqtrd', '( %s -> ( ( C x. G ) x. A ) = ( G x. ( C x. A ) ) )' % A)
m3 = w.s([m2, e3], 'breqtrd', '( %s -> ( ; 6 0 x. A ) <_ ( G x. ( C x. A ) ) )' % A)
g0e = w.s([g0], 'ltled', '( %s -> 0 <_ G )' % A)
m4 = w.s([w.s([cr, ar], 'remulcld', '( %s -> ( C x. A ) e. RR )' % A), sixpp, gr, g0e, ca], 'lemul2ad',
         '( %s -> ( G x. ( C x. A ) ) <_ ( G x. ( 6 x. %s ) ) )' % (A, PP))
e4 = w.s([gc, r6cd, ppc], 'mul12d', '( %s -> ( G x. ( 6 x. %s ) ) = ( 6 x. ( G x. %s ) ) )' % (A, PP, PP))
m5 = w.s([m4, e4], 'breqtrd', '( %s -> ( G x. ( C x. A ) ) <_ ( 6 x. ( G x. %s ) ) )' % (A, PP))
gpp = w.s([gr, ppr], 'remulcld', '( %s -> ( G x. %s ) e. RR )' % (A, PP))
m6 = w.s([w.s([r60, ar], 'remulcld', '( %s -> ( ; 6 0 x. A ) e. RR )' % A),
          w.s([gr, w.s([cr, ar], 'remulcld', '( %s -> ( C x. A ) e. RR )' % A)], 'remulcld', '( %s -> ( G x. ( C x. A ) ) e. RR )' % A),
          w.s([w.s([w.s([], '6re', '6 e. RR')], 'a1i', '( %s -> 6 e. RR )' % A), gpp], 'remulcld', '( %s -> ( 6 x. ( G x. %s ) ) e. RR )' % (A, PP)),
          m3, m5], 'letrd', '( %s -> ( ; 6 0 x. A ) <_ ( 6 x. ( G x. %s ) ) )' % (A, PP))
linarith(w, A, [m6], '( ; 1 0 x. A ) <_ ( G x. %s )' % PP, leaves={'A': ar, '( G x. %s )' % PP: gpp}, name='qed')
run(w)
