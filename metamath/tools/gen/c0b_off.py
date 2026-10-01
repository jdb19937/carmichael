"""Sortie C0b, batch 12: Cauchy-Goursat off one point (softmin, rectintgnz,
rectintmb, rectintgour1)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')

# ---- softmin
w = W('softmin', 'The harmonic-type product of two positive reals is positive and below both.')
A0 = '( A e. RR+ /\\ B e. RR+ )'
MN = '( ( A x. B ) / ( A + B ) )'
arp = w.s([], 'simpl', '( %s -> A e. RR+ )' % A0)
brp = w.s([], 'simpr', '( %s -> B e. RR+ )' % A0)
sm = w.s([arp, brp], 'rpaddcld', '( %s -> ( A + B ) e. RR+ )' % A0)
pr = w.s([arp, brp], 'rpmulcld', '( %s -> ( A x. B ) e. RR+ )' % A0)
mrp = w.s([pr, sm], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, MN))
are = w.s([arp, w.inst('rpre')], 'syl', '( %s -> A e. RR )' % A0)
bre = w.s([brp, w.inst('rpre')], 'syl', '( %s -> B e. RR )' % A0)
prr = w.s([pr, w.inst('rpre')], 'syl', '( %s -> ( A x. B ) e. RR )' % A0)
ac = w.s([are], 'recnd', '( %s -> A e. CC )' % A0)
bc = w.s([bre], 'recnd', '( %s -> B e. CC )' % A0)
bge = w.s([brp, w.inst('rpge0')], 'syl', '( %s -> 0 <_ B )' % A0)
age = w.s([arp, w.inst('rpge0')], 'syl', '( %s -> 0 <_ A )' % A0)
# ( A x. B ) <_ ( ( A + B ) x. A ) since B <_ ( A + B )
ble = w.s([bre, w.s([are, bre], 'readdcld', '( %s -> ( A + B ) e. RR )' % A0), age, w.s([bre, are], 'addge01d' if False else 'id', 'x')], 'id', 'y')
w.lines.pop(); w.lines.pop()
bsum = w.s([w.s([bre, are], 'addge02d', '( %s -> ( 0 <_ A <-> B <_ ( A + B ) ) )' % A0), age], 'mpbid', '( %s -> B <_ ( A + B ) )' % A0)
asum = w.s([w.s([are, bre], 'addge01d', '( %s -> ( 0 <_ B <-> A <_ ( A + B ) ) )' % A0), bge], 'mpbid', '( %s -> A <_ ( A + B ) )' % A0)
mul1 = w.s([w.s([bre, w.s([are, bre], 'readdcld', '( %s -> ( A + B ) e. RR )' % A0), w.s([are, age], 'jca', '( %s -> ( A e. RR /\\ 0 <_ A ) )' % A0)], '3jca',
                '( %s -> ( B e. RR /\\ ( A + B ) e. RR /\\ ( A e. RR /\\ 0 <_ A ) ) )' % A0), bsum, w.inst('lemul2a')], 'syl2anc',
           '( %s -> ( A x. B ) <_ ( A x. ( A + B ) ) )' % A0)
d1 = w.s([w.s([prr, are, sm], 'ledivmuld', '( %s -> ( %s <_ A <-> ( A x. B ) <_ ( ( A + B ) x. A ) ) )' % (A0, MN)),
          w.s([mul1, w.s([ac, w.s([ac, bc], 'addcld', '( %s -> ( A + B ) e. CC )' % A0)], 'mulcomd', '( %s -> ( A x. ( A + B ) ) = ( ( A + B ) x. A ) )' % A0)], 'breqtrd', '( %s -> ( A x. B ) <_ ( ( A + B ) x. A ) )' % A0)], 'mpbird',
         '( %s -> %s <_ A )' % (A0, MN))
mul2 = w.s([w.s([are, w.s([are, bre], 'readdcld', '( %s -> ( A + B ) e. RR )' % A0), w.s([bre, bge], 'jca', '( %s -> ( B e. RR /\\ 0 <_ B ) )' % A0)], '3jca',
                '( %s -> ( A e. RR /\\ ( A + B ) e. RR /\\ ( B e. RR /\\ 0 <_ B ) ) )' % A0), asum, w.inst('lemul1a')], 'syl2anc',
           '( %s -> ( A x. B ) <_ ( ( A + B ) x. B ) )' % A0)
d2 = w.s([w.s([prr, bre, sm], 'ledivmuld', '( %s -> ( %s <_ B <-> ( A x. B ) <_ ( ( A + B ) x. B ) ) )' % (A0, MN)), mul2], 'mpbird', '( %s -> %s <_ B )' % (A0, MN))
w.qed([mrp, w.s([d1, d2], 'jca', '( %s -> ( %s <_ A /\\ %s <_ B ) )' % (A0, MN, MN))], 'jca', '( %s -> ( %s e. RR+ /\\ ( %s <_ A /\\ %s <_ B ) ) )' % (A0, MN, MN, MN)); run(w)

# ---- rectintgnz
w = W('rectintgnz', 'A sub-rectangle missing the exceptional point has zero boundary integral.')
HOL = '( F e. ( D -cn-> CC ) /\\ ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) )'
SUB = '( ( U e. CC /\\ W e. CC ) /\\ ( ( Re ` U ) <_ ( Re ` W ) /\\ ( Im ` U ) <_ ( Im ` W ) ) /\\ ( ( U crect W ) C_ ( A crect B ) /\\ -. P e. ( U crect W ) ) )'
A0 = '( %s /\\ %s )' % (HOL, SUB)
fcn = w.s([], 'simpll', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dvs = w.s([], 'simplr', '( %s -> ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) )' % A0)
uw = w.s([], 'simpr1', '( %s -> ( U e. CC /\\ W e. CC ) )' % A0)
ord = w.s([], 'simpr2', '( %s -> ( ( Re ` U ) <_ ( Re ` W ) /\\ ( Im ` U ) <_ ( Im ` W ) ) )' % A0)
inc = w.s([], 'simpr3l' if False else 'simpr3', 'x')
w.lines.pop()
p3 = w.s([], 'simpr3', '( %s -> ( ( U crect W ) C_ ( A crect B ) /\\ -. P e. ( U crect W ) ) )' % A0)
inc = w.s([p3, w.inst('simpl')], 'syl', '( %s -> ( U crect W ) C_ ( A crect B ) )' % A0)
npp = w.s([p3, w.inst('simpr')], 'syl', '( %s -> -. P e. ( U crect W ) )' % A0)
AZ = '( %s /\\ z e. ( U crect W ) )' % A0
zuw = w.s([], 'simpr', '( %s -> z e. ( U crect W ) )' % AZ)
zab = w.s([w.s([inc], 'adantr', '( %s -> ( U crect W ) C_ ( A crect B ) )' % AZ), zuw], 'sseldd', '( %s -> z e. ( A crect B ) )' % AZ)
npz = w.s([w.s([npp], 'adantr', '( %s -> -. P e. ( U crect W ) )' % AZ)], 'olcd' if False else 'id', 'x')
w.lines.pop()
zne = w.s([w.s([], 'eleq1', '( z = P -> ( z e. ( U crect W ) <-> P e. ( U crect W ) ) )'), zuw, w.s([npp], 'adantr', '( %s -> -. P e. ( U crect W ) )' % AZ)], 'id' if False else 'id', 'y')
w.lines.pop()
elp = w.s([], 'eleq1', '( z = P -> ( z e. ( U crect W ) <-> P e. ( U crect W ) ) )')
zpi = w.s([zuw, w.s([elp], 'a1i', '( %s -> ( z = P -> ( z e. ( U crect W ) <-> P e. ( U crect W ) ) ) )' % AZ)], 'id' if False else 'id', 'z')
w.lines.pop()
zne = w.s([w.s([w.s([elp], 'biimpd', '( z = P -> ( z e. ( U crect W ) -> P e. ( U crect W ) ) )')], 'com12', '( z e. ( U crect W ) -> ( z = P -> P e. ( U crect W ) ) )'), zuw], 'syl' if False else 'id', 'q')
w.lines.pop()
imp1 = w.s([w.s([elp], 'biimpd', '( z = P -> ( z e. ( U crect W ) -> P e. ( U crect W ) ) )')], 'com12', '( z e. ( U crect W ) -> ( z = P -> P e. ( U crect W ) ) )')
imp2 = w.s([zuw, w.s([imp1], 'a1i', '( %s -> ( z e. ( U crect W ) -> ( z = P -> P e. ( U crect W ) ) ) )' % AZ)], 'mpd', '( %s -> ( z = P -> P e. ( U crect W ) ) )' % AZ)
zne = w.s([w.s([npp], 'adantr', '( %s -> -. P e. ( U crect W ) )' % AZ), imp2], 'mtod', '( %s -> -. z = P )' % AZ)
zned = w.s([zne], 'neqned', '( %s -> z =/= P )' % AZ)
zdif = w.s([w.s([zab, zned], 'jca', '( %s -> ( z e. ( A crect B ) /\\ z =/= P ) )' % AZ), w.s([closed(w, AZ, 'eldifsn', '( z e. ( ( A crect B ) \\ { P } ) <-> ( z e. ( A crect B ) /\\ z =/= P ) )')], 'id' if False else 'id', 'r')], 'id', 's')
w.lines.pop(); w.lines.pop()
eds = closed(w, AZ, 'eldifsn', '( z e. ( ( A crect B ) \\ { P } ) <-> ( z e. ( A crect B ) /\\ z =/= P ) )')
zdif = w.s([eds, w.s([zab, zned], 'jca', '( %s -> ( z e. ( A crect B ) /\\ z =/= P ) )' % AZ)], 'mpbird', '( %s -> z e. ( ( A crect B ) \\ { P } ) )' % AZ)
ssd = w.s([w.s([zdif], 'ex', '( %s -> ( z e. ( U crect W ) -> z e. ( ( A crect B ) \\ { P } ) ) )' % A0)], 'ssrdv', '( %s -> ( U crect W ) C_ ( ( A crect B ) \\ { P } ) )' % A0)
w.qed([uw, ord, w.s([fcn, w.s([ssd, dvs], 'sstrd', '( %s -> ( U crect W ) C_ dom ( CC _D F ) )' % A0)], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( U crect W ) C_ dom ( CC _D F ) ) )' % A0), w.inst('rectintgour')], 'syl3anc',
      '( %s -> ( F rectint <. U , W >. ) = 0 )' % A0); run(w)

# ---- rectintmb: the bound on a small rectangle around the exceptional point
DM = '( ( ( Re ` W ) - ( Re ` U ) ) + ( ( Im ` W ) - ( Im ` U ) ) )'
KP = '( ( abs ` ( F ` P ) ) + 1 )'
def CN(t):
    return '( ( abs ` ( %s - P ) ) < Q -> ( abs ` ( ( F ` %s ) - ( F ` P ) ) ) < 1 )' % (t, t)
CNA = 'A. s e. D %s' % CN('s')
w = W('rectintmb', 'The boundary integral over a small rectangle around a point is bounded by the perimeter times a local bound.')
B1 = '( F e. ( D -cn-> CC ) /\\ P e. D )'
B2 = '( Q e. RR+ /\\ %s )' % CNA
B3 = '( ( U e. CC /\\ W e. CC ) /\\ ( ( Re ` U ) <_ ( Re ` W ) /\\ ( Im ` U ) <_ ( Im ` W ) ) /\\ ( ( U crect W ) C_ D /\\ P e. ( U crect W ) /\\ %s < Q ) )' % DM
A0 = '( %s /\\ %s /\\ %s )' % (B1, B2, B3)
b1 = w.s([], 'simp1', '( %s -> %s )' % (A0, B1))
b2 = w.s([], 'simp2', '( %s -> %s )' % (A0, B2))
b3 = w.s([], 'simp3', '( %s -> %s )' % (A0, B3))
fcn = w.s([b1, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pd = w.s([b1, w.inst('simpr')], 'syl', '( %s -> P e. D )' % A0)
qrp = w.s([b2, w.inst('simpl')], 'syl', '( %s -> Q e. RR+ )' % A0)
cna = w.s([b2, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, CNA))
uwp = w.s([b3, w.inst('simp1')], 'syl', '( %s -> ( U e. CC /\\ W e. CC ) )' % A0)
ord = w.s([b3, w.inst('simp2')], 'syl', '( %s -> ( ( Re ` U ) <_ ( Re ` W ) /\\ ( Im ` U ) <_ ( Im ` W ) ) )' % A0)
p3 = w.s([b3, w.inst('simp3')], 'syl', '( %s -> ( ( U crect W ) C_ D /\\ P e. ( U crect W ) /\\ %s < Q ) )' % (A0, DM))
uss = w.s([p3, w.inst('simp1')], 'syl', '( %s -> ( U crect W ) C_ D )' % A0)
pin = w.s([p3, w.inst('simp2')], 'syl', '( %s -> P e. ( U crect W ) )' % A0)
dlt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s < Q )' % (A0, DM))
uc = w.s([uwp, w.inst('simpl')], 'syl', '( %s -> U e. CC )' % A0)
wc = w.s([uwp, w.inst('simpr')], 'syl', '( %s -> W e. CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
pc = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
fpc = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
fpr = w.s([fpc], 'abscld', '( %s -> ( abs ` ( F ` P ) ) e. RR )' % A0)
kr = w.s([fpr, closed(w, A0, '1re', '1 e. RR')], 'readdcld', '( %s -> %s e. RR )' % (A0, KP))
ur = w.s([uc, w.inst('recl')], 'syl', '( %s -> ( Re ` U ) e. RR )' % A0)
wr = w.s([wc, w.inst('recl')], 'syl', '( %s -> ( Re ` W ) e. RR )' % A0)
ui = w.s([uc, w.inst('imcl')], 'syl', '( %s -> ( Im ` U ) e. RR )' % A0)
wi = w.s([wc, w.inst('imcl')], 'syl', '( %s -> ( Im ` W ) e. RR )' % A0)
dmr = w.s([w.s([wr, ur], 'resubcld', '( %s -> ( ( Re ` W ) - ( Re ` U ) ) e. RR )' % A0), w.s([wi, ui], 'resubcld', '( %s -> ( ( Im ` W ) - ( Im ` U ) ) e. RR )' % A0)], 'readdcld', '( %s -> %s e. RR )' % (A0, DM))
elcb = w.s([uwp, w.inst('elcrect')], 'syl', '( %s -> ( P e. ( U crect W ) <-> ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` P ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) ) )' % A0)
ptt = w.s([pin, elcb], 'mpbid', '( %s -> ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` P ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) )' % A0)
pre = w.s([ptt, w.inst('simp2')], 'syl', '( %s -> ( Re ` P ) e. ( ( Re ` U ) [,] ( Re ` W ) ) )' % A0)
pim = w.s([ptt, w.inst('simp3')], 'syl', '( %s -> ( Im ` P ) e. ( ( Im ` U ) [,] ( Im ` W ) ) )' % A0)
# the pointwise bound
AZ = '( %s /\\ z e. ( U crect W ) )' % A0
zz = w.s([], 'simpr', '( %s -> z e. ( U crect W ) )' % AZ)
def dn(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (AZ, f))
ffz = dn(ff, 'F : D --> CC'); ussz = dn(uss, '( U crect W ) C_ D'); dssz = dn(dss, 'D C_ CC')
ucz = dn(uc, 'U e. CC'); wcz = dn(wc, 'W e. CC'); pcz = dn(pc, 'P e. CC'); fpcz = dn(fpc, '( F ` P ) e. CC')
urz = dn(ur, '( Re ` U ) e. RR'); wrz = dn(wr, '( Re ` W ) e. RR'); uiz = dn(ui, '( Im ` U ) e. RR'); wiz = dn(wi, '( Im ` W ) e. RR')
prez = dn(pre, '( Re ` P ) e. ( ( Re ` U ) [,] ( Re ` W ) )'); pimz = dn(pim, '( Im ` P ) e. ( ( Im ` U ) [,] ( Im ` W ) )')
dmrz = dn(dmr, '%s e. RR' % DM); dltz = dn(dlt, '%s < Q' % DM); qrpz = dn(qrp, 'Q e. RR+'); cnaz = dn(cna, CNA)
fprz = dn(fpr, '( abs ` ( F ` P ) ) e. RR'); krz = dn(kr, '%s e. RR' % KP)
zd = w.s([ussz, zz], 'sseldd', '( %s -> z e. D )' % AZ)
zcc = w.s([dssz, zd], 'sseldd', '( %s -> z e. CC )' % AZ)
elcz = w.s([w.s([ucz, wcz], 'jca', '( %s -> ( U e. CC /\\ W e. CC ) )' % AZ), w.inst('elcrect')], 'syl',
           '( %s -> ( z e. ( U crect W ) <-> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) ) )' % AZ)
ztt = w.s([zz, elcz], 'mpbid', '( %s -> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) )' % AZ)
zre = w.s([ztt, w.inst('simp2')], 'syl', '( %s -> ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) )' % AZ)
zim = w.s([ztt, w.inst('simp3')], 'syl', '( %s -> ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) )' % AZ)
sub = w.s([zcc, pcz], 'subcld', '( %s -> ( z - P ) e. CC )' % AZ)
rsu = w.s([w.s([zcc, pcz, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( z - P ) ) = ( ( Re ` z ) - ( Re ` P ) ) )' % AZ)], 'fveq2d', '( %s -> ( abs ` ( Re ` ( z - P ) ) ) = ( abs ` ( ( Re ` z ) - ( Re ` P ) ) ) )' % AZ)
isu = w.s([w.s([zcc, pcz, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` ( z - P ) ) = ( ( Im ` z ) - ( Im ` P ) ) )' % AZ)], 'fveq2d', '( %s -> ( abs ` ( Im ` ( z - P ) ) ) = ( abs ` ( ( Im ` z ) - ( Im ` P ) ) ) )' % AZ)
ar1 = w.s([rsu, w.s([w.s([urz, wrz], 'jca', '( %s -> ( ( Re ` U ) e. RR /\\ ( Re ` W ) e. RR ) )' % AZ), w.s([zre, prez], 'jca', '( %s -> ( ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Re ` P ) e. ( ( Re ` U ) [,] ( Re ` W ) ) ) )' % AZ), w.inst('iccabssub')], 'syl2anc',
               '( %s -> ( abs ` ( ( Re ` z ) - ( Re ` P ) ) ) <_ ( ( Re ` W ) - ( Re ` U ) ) )' % AZ)], 'eqbrtrd', '( %s -> ( abs ` ( Re ` ( z - P ) ) ) <_ ( ( Re ` W ) - ( Re ` U ) ) )' % AZ)
ar2 = w.s([isu, w.s([w.s([uiz, wiz], 'jca', '( %s -> ( ( Im ` U ) e. RR /\\ ( Im ` W ) e. RR ) )' % AZ), w.s([zim, pimz], 'jca', '( %s -> ( ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) /\\ ( Im ` P ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) )' % AZ), w.inst('iccabssub')], 'syl2anc',
               '( %s -> ( abs ` ( ( Im ` z ) - ( Im ` P ) ) ) <_ ( ( Im ` W ) - ( Im ` U ) ) )' % AZ)], 'eqbrtrd', '( %s -> ( abs ` ( Im ` ( z - P ) ) ) <_ ( ( Im ` W ) - ( Im ` U ) ) )' % AZ)
arr = w.s([w.s([w.s([sub, w.inst('recl')], 'syl', '( %s -> ( Re ` ( z - P ) ) e. RR )' % AZ)], 'recnd', '( %s -> ( Re ` ( z - P ) ) e. CC )' % AZ)], 'abscld', '( %s -> ( abs ` ( Re ` ( z - P ) ) ) e. RR )' % AZ)
aii = w.s([w.s([w.s([sub, w.inst('imcl')], 'syl', '( %s -> ( Im ` ( z - P ) ) e. RR )' % AZ)], 'recnd', '( %s -> ( Im ` ( z - P ) ) e. CC )' % AZ)], 'abscld', '( %s -> ( abs ` ( Im ` ( z - P ) ) ) e. RR )' % AZ)
sm2 = w.s([arr, aii, w.s([wrz, urz], 'resubcld', '( %s -> ( ( Re ` W ) - ( Re ` U ) ) e. RR )' % AZ), w.s([wiz, uiz], 'resubcld', '( %s -> ( ( Im ` W ) - ( Im ` U ) ) e. RR )' % AZ), ar1, ar2], 'le2addd',
          '( %s -> ( ( abs ` ( Re ` ( z - P ) ) ) + ( abs ` ( Im ` ( z - P ) ) ) ) <_ %s )' % (AZ, DM))
absz = w.s([sub], 'abscld', '( %s -> ( abs ` ( z - P ) ) e. RR )' % AZ)
dist = w.s([absz, w.s([arr, aii], 'readdcld', '( %s -> ( ( abs ` ( Re ` ( z - P ) ) ) + ( abs ` ( Im ` ( z - P ) ) ) ) e. RR )' % AZ), dmrz,
            w.s([sub, w.inst('abscrle')], 'syl', '( %s -> ( abs ` ( z - P ) ) <_ ( ( abs ` ( Re ` ( z - P ) ) ) + ( abs ` ( Im ` ( z - P ) ) ) ) )' % AZ), sm2], 'letrd', '( %s -> ( abs ` ( z - P ) ) <_ %s )' % (AZ, DM))
ltq = w.s([absz, dmrz, w.s([qrpz, w.inst('rpre')], 'syl', '( %s -> Q e. RR )' % AZ), dist, dltz], 'lelttrd', '( %s -> ( abs ` ( z - P ) ) < Q )' % AZ)
sb1 = w.s([], 'oveq1', '( s = z -> ( s - P ) = ( z - P ) )')
sb2 = w.s([w.s([sb1], 'fveq2d', '( s = z -> ( abs ` ( s - P ) ) = ( abs ` ( z - P ) ) )')], 'breq1d', '( s = z -> ( ( abs ` ( s - P ) ) < Q <-> ( abs ` ( z - P ) ) < Q ) )')
sb3 = w.s([w.s([w.s([w.s([], 'fveq2', '( s = z -> ( F ` s ) = ( F ` z ) )')], 'oveq1d', '( s = z -> ( ( F ` s ) - ( F ` P ) ) = ( ( F ` z ) - ( F ` P ) ) )')], 'fveq2d',
               '( s = z -> ( abs ` ( ( F ` s ) - ( F ` P ) ) ) = ( abs ` ( ( F ` z ) - ( F ` P ) ) ) )')], 'breq1d',
          '( s = z -> ( ( abs ` ( ( F ` s ) - ( F ` P ) ) ) < 1 <-> ( abs ` ( ( F ` z ) - ( F ` P ) ) ) < 1 ) )')
sbb = w.s([sb2, sb3], 'imbi12d', '( s = z -> ( %s <-> %s ) )' % (CN('s'), CN('z')))
ins = w.s([sbb, cnaz, zd], 'rspcdva', '( %s -> %s )' % (AZ, CN('z')))
lt1 = w.s([ltq, ins], 'mpd', '( %s -> ( abs ` ( ( F ` z ) - ( F ` P ) ) ) < 1 )' % AZ)
fzc = w.s([ffz, zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % AZ)
dfc = w.s([fzc, fpcz], 'subcld', '( %s -> ( ( F ` z ) - ( F ` P ) ) e. CC )' % AZ)
adf = w.s([dfc], 'abscld', '( %s -> ( abs ` ( ( F ` z ) - ( F ` P ) ) ) e. RR )' % AZ)
tri = w.s([w.s([w.s([dfc, fpcz], 'abstrid', '( %s -> ( abs ` ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) ) <_ ( ( abs ` ( ( F ` z ) - ( F ` P ) ) ) + ( abs ` ( F ` P ) ) ) )' % AZ),
                w.s([w.s([fzc, fpcz], 'npcand', '( %s -> ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) = ( F ` z ) )' % AZ)], 'fveq2d', '( %s -> ( abs ` ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) ) = ( abs ` ( F ` z ) ) )' % AZ)], 'breqtrrd' if False else 'id', 'x')], 'id', 'y')
w.lines.pop(); w.lines.pop()
tri0 = w.s([dfc, fpcz], 'abstrid', '( %s -> ( abs ` ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) ) <_ ( ( abs ` ( ( F ` z ) - ( F ` P ) ) ) + ( abs ` ( F ` P ) ) ) )' % AZ)
npc = w.s([w.s([fzc, fpcz], 'npcand', '( %s -> ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) = ( F ` z ) )' % AZ)], 'eqcomd', '( %s -> ( F ` z ) = ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) )' % AZ)
tri = w.s([w.s([npc], 'fveq2d', '( %s -> ( abs ` ( F ` z ) ) = ( abs ` ( ( ( F ` z ) - ( F ` P ) ) + ( F ` P ) ) ) )' % AZ), tri0], 'eqbrtrd',
          '( %s -> ( abs ` ( F ` z ) ) <_ ( ( abs ` ( ( F ` z ) - ( F ` P ) ) ) + ( abs ` ( F ` P ) ) ) )' % AZ)
add1 = w.s([adf, closed(w, AZ, '1re', '1 e. RR'), fprz, w.s([adf, closed(w, AZ, '1re', '1 e. RR'), lt1], 'ltled', '( %s -> ( abs ` ( ( F ` z ) - ( F ` P ) ) ) <_ 1 )' % AZ)], 'leadd1dd' if False else 'id', 'z')
w.lines.pop()
le1 = w.s([adf, closed(w, AZ, '1re', '1 e. RR'), lt1], 'ltled', '( %s -> ( abs ` ( ( F ` z ) - ( F ` P ) ) ) <_ 1 )' % AZ)
add1 = w.s([adf, closed(w, AZ, '1re', '1 e. RR'), fprz, fprz, le1, w.s([fprz], 'leidd', '( %s -> ( abs ` ( F ` P ) ) <_ ( abs ` ( F ` P ) ) )' % AZ)], 'le2addd',
           '( %s -> ( ( abs ` ( ( F ` z ) - ( F ` P ) ) ) + ( abs ` ( F ` P ) ) ) <_ ( 1 + ( abs ` ( F ` P ) ) ) )' % AZ)
cmm = w.s([closed(w, AZ, 'ax-1cn', '1 e. CC'), w.s([fprz], 'recnd', '( %s -> ( abs ` ( F ` P ) ) e. CC )' % AZ)], 'addcomd', '( %s -> ( 1 + ( abs ` ( F ` P ) ) ) = %s )' % (AZ, KP))
ptb = w.s([w.s([fzc], 'abscld', '( %s -> ( abs ` ( F ` z ) ) e. RR )' % AZ), w.s([adf, fprz], 'readdcld', '( %s -> ( ( abs ` ( ( F ` z ) - ( F ` P ) ) ) + ( abs ` ( F ` P ) ) ) e. RR )' % AZ), krz,
            tri, w.s([add1, cmm], 'breqtrd', '( %s -> ( ( abs ` ( ( F ` z ) - ( F ` P ) ) ) + ( abs ` ( F ` P ) ) ) <_ %s )' % (AZ, KP))], 'letrd', '( %s -> ( abs ` ( F ` z ) ) <_ %s )' % (AZ, KP))
ral = w.s([ptb], 'ralrimiva', '( %s -> A. z e. ( U crect W ) ( abs ` ( F ` z ) ) <_ %s )' % (A0, KP))
psuw = w.s([uwp, ord, w.s([fcn, uss], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( U crect W ) C_ D ) )' % A0)], '3jca', '( %s -> %s )' % (A0, PSOF('U', 'W')))
w.qed([psuw, kr, ral, w.inst('rectintabs')], 'syl3anc', '( %s -> ( abs ` ( F rectint <. U , W >. ) ) <_ ( ( 2 x. %s ) x. %s ) )' % (A0, KP, DM)); run(w)

# ---- rectintg1a: the estimate for a fixed grid around the exceptional point
HOL1 = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) )'
def CN2(t):
    return '( ( abs ` ( %s - P ) ) < Q -> ( abs ` ( ( F ` %s ) - ( F ` P ) ) ) < 1 )' % (t, t)
CNA2 = 'A. s e. D %s' % CN2('s')
GX = '( ( X e. RR /\\ Y e. RR ) /\\ ( %s < X /\\ X <_ Y /\\ Y < %s ) )' % (RA, RB)
GY = '( ( S e. RR /\\ T e. RR ) /\\ ( %s < S /\\ S <_ T /\\ T < %s ) )' % (IA, IB)
MID = '( ( X < ( Re ` P ) /\\ ( Re ` P ) < Y ) /\\ ( S < ( Im ` P ) /\\ ( Im ` P ) < T ) )'
DMG = '( ( Y - X ) + ( T - S ) )'
CQ = '( Q e. RR+ /\\ %s < Q /\\ %s )' % (DMG, CNA2)
A0 = '( ( %s /\\ ( P e. CC /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (AB, HOL1, GX, GY, MID, CQ)
w = W('rectintg1a', 'The boundary integral is bounded by the perimeter of a small rectangle around the exceptional point.')
ab = w.s([], 'simp1l', '( %s -> %s )' % (A0, AB))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ph1 = w.s([], 'simp1r', '( %s -> ( P e. CC /\\ %s ) )' % (A0, HOL1))
pc = w.s([ph1, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
hol = w.s([ph1, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, HOL1))
fcn = w.s([hol, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rssd = w.s([hol, w.inst('simp2')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
dvs = w.s([hol, w.inst('simp3')], 'syl', '( %s -> ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) )' % A0)
gx = w.s([], 'simp2l', '( %s -> %s )' % (A0, GX))
gy = w.s([], 'simp2r', '( %s -> %s )' % (A0, GY))
mid = w.s([], 'simp3l', '( %s -> %s )' % (A0, MID))
cq = w.s([], 'simp3r', '( %s -> %s )' % (A0, CQ))
xr = w.s([w.s([gx, w.inst('simpl')], 'syl', '( %s -> ( X e. RR /\\ Y e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> X e. RR )' % A0)
yr = w.s([w.s([gx, w.inst('simpl')], 'syl', '( %s -> ( X e. RR /\\ Y e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> Y e. RR )' % A0)
sr = w.s([w.s([gy, w.inst('simpl')], 'syl', '( %s -> ( S e. RR /\\ T e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
tr = w.s([w.s([gy, w.inst('simpl')], 'syl', '( %s -> ( S e. RR /\\ T e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> T e. RR )' % A0)
gxi = w.s([gx, w.inst('simpr')], 'syl', '( %s -> ( %s < X /\\ X <_ Y /\\ Y < %s ) )' % (A0, RA, RB))
gyi = w.s([gy, w.inst('simpr')], 'syl', '( %s -> ( %s < S /\\ S <_ T /\\ T < %s ) )' % (A0, IA, IB))
ax = w.s([gxi, w.inst('simp1')], 'syl', '( %s -> %s < X )' % (A0, RA))
xy = w.s([gxi, w.inst('simp2')], 'syl', '( %s -> X <_ Y )' % A0)
yB = w.s([gxi, w.inst('simp3')], 'syl', '( %s -> Y < %s )' % (A0, RB))
as_ = w.s([gyi, w.inst('simp1')], 'syl', '( %s -> %s < S )' % (A0, IA))
st = w.s([gyi, w.inst('simp2')], 'syl', '( %s -> S <_ T )' % A0)
tB = w.s([gyi, w.inst('simp3')], 'syl', '( %s -> T < %s )' % (A0, IB))
xp_ = w.s([w.s([mid, w.inst('simpl')], 'syl', '( %s -> ( X < ( Re ` P ) /\\ ( Re ` P ) < Y ) )' % A0), w.inst('simpl')], 'syl', '( %s -> X < ( Re ` P ) )' % A0)
py = w.s([w.s([mid, w.inst('simpl')], 'syl', '( %s -> ( X < ( Re ` P ) /\\ ( Re ` P ) < Y ) )' % A0), w.inst('simpr')], 'syl', '( %s -> ( Re ` P ) < Y )' % A0)
sp_ = w.s([w.s([mid, w.inst('simpr')], 'syl', '( %s -> ( S < ( Im ` P ) /\\ ( Im ` P ) < T ) )' % A0), w.inst('simpl')], 'syl', '( %s -> S < ( Im ` P ) )' % A0)
pt_ = w.s([w.s([mid, w.inst('simpr')], 'syl', '( %s -> ( S < ( Im ` P ) /\\ ( Im ` P ) < T ) )' % A0), w.inst('simpr')], 'syl', '( %s -> ( Im ` P ) < T )' % A0)
qrp = w.s([cq, w.inst('simp1')], 'syl', '( %s -> Q e. RR+ )' % A0)
dq = w.s([cq, w.inst('simp2')], 'syl', '( %s -> %s < Q )' % (A0, DMG))
cna = w.s([cq, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, CNA2))
ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc, w.inst('recl')], 'syl', '( %s -> ( Re ` P ) e. RR )' % A0)
pi_ = w.s([pc, w.inst('imcl')], 'syl', '( %s -> ( Im ` P ) e. RR )' % A0)
ic = closed(w, A0, 'ax-icn', '_i e. CC')
rl = {RA: ar, RB: br, IA: ai, IB: bi, 'X': xr, 'Y': yr, 'S': sr, 'T': tr}
cs = {k: w.s([v], 'recnd', '( %s -> %s e. CC )' % (A0, k)) for k, v in rl.items()}
ptc = {}; ptre = {}; ptim = {}
for (u, v) in [('X', IA), ('X', IB), ('Y', IA), ('Y', IB), ('X', 'S'), ('X', 'T'), ('Y', 'S'), ('Y', 'T')]:
    p = PT(u, v)
    ptc[p] = w.s([cs[u], w.s([ic, cs[v]], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, v))], 'addcld', '( %s -> %s e. CC )' % (A0, p))
    ptre[p] = w.s([rl[u], rl[v], w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, p, u))
    ptim[p] = w.s([rl[u], rl[v], w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, p, v))
CCS = {'A': ac, 'B': bc}; CCS.update(ptc)
eqR = {'A': w.s([], 'eqidd', '( %s -> ( Re ` A ) = ( Re ` A ) )' % A0), 'B': w.s([], 'eqidd', '( %s -> ( Re ` B ) = ( Re ` B ) )' % A0)}
eqI = {'A': w.s([], 'eqidd', '( %s -> ( Im ` A ) = ( Im ` A ) )' % A0), 'B': w.s([], 'eqidd', '( %s -> ( Im ` B ) = ( Im ` B ) )' % A0)}
def cR(P): return eqR[P] if P in ('A', 'B') else ptre[P]
def cI(P): return eqI[P] if P in ('A', 'B') else ptim[P]
lid = {k: w.s([v], 'leidd', '( %s -> %s <_ %s )' % (A0, k, k)) for k, v in rl.items()}
leax = w.s([ar, xr, ax], 'ltled', '( %s -> %s <_ X )' % (A0, RA))
leyB = w.s([yr, br, yB], 'ltled', '( %s -> Y <_ %s )' % (A0, RB))
leas = w.s([ai, sr, as_], 'ltled', '( %s -> %s <_ S )' % (A0, IA))
letB = w.s([tr, bi, tB], 'ltled', '( %s -> T <_ %s )' % (A0, IB))
xB = w.s([xr, yr, br, xy, yB], 'lelttrd', '( %s -> X < %s )' % (A0, RB))
lexB = w.s([xr, br, xB], 'ltled', '( %s -> X <_ %s )' % (A0, RB))
aY = w.s([ar, xr, yr, ax, xy], 'ltletrd', '( %s -> %s < Y )' % (A0, RA))
leaY = w.s([ar, yr, aY], 'ltled', '( %s -> %s <_ Y )' % (A0, RA))
sB = w.s([sr, tr, bi, st, tB], 'lelttrd', '( %s -> S < %s )' % (A0, IB))
lesB = w.s([sr, bi, sB], 'ltled', '( %s -> S <_ %s )' % (A0, IB))
aT = w.s([ai, sr, tr, as_, st], 'ltletrd', '( %s -> %s < T )' % (A0, IA))
leaT = w.s([ai, tr, aT], 'ltled', '( %s -> %s <_ T )' % (A0, IA))
leaI = w.s([ai, bi, w.s([ai, sr, bi, as_, sB], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))


def incl(P, Q, loR, hiR, loI, hiI):
    c1 = w.s([loR, cR(P)], 'breqtrrd', '( %s -> %s <_ ( Re ` %s ) )' % (A0, RA, P))
    c2 = w.s([cR(Q), hiR], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ %s )' % (A0, Q, RB))
    c3 = w.s([loI, cI(P)], 'breqtrrd', '( %s -> %s <_ ( Im ` %s ) )' % (A0, IA, P))
    c4 = w.s([cI(Q), hiI], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ %s )' % (A0, Q, IB))
    inc = w.s([w.s([c1, c2], 'jca', '( %s -> ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) )' % (A0, RA, P, Q, RB)),
               w.s([c3, c4], 'jca', '( %s -> ( %s <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ %s ) )' % (A0, IA, P, Q, IB))], 'jca',
              '( %s -> ( ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) /\\ ( %s <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ %s ) ) )' % (A0, RA, P, Q, RB, IA, P, Q, IB))
    return w.s([ab, w.s([CCS[P], CCS[Q]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, P, Q)), inc, w.inst('crectss2')], 'syl3anc', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, P, Q))


def notin(P, Q, part, val, cl, lop, hip, strict, which):
    """-. P e. ( P' crect Q' ); which='lo' means the coordinate is above the upper bound"""
    elc = w.s([w.s([CCS[P], CCS[Q]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, P, Q)), w.inst('elcrect')], 'syl',
              '( %s -> ( P e. ( %s crect %s ) <-> ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` P ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A0, P, Q, P, Q, P, Q))
    sel = 'simp2' if part == 'Re' else 'simp3'
    mem = w.s([w.s([elc], 'biimpd', '( %s -> ( P e. ( %s crect %s ) -> ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` P ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A0, P, Q, P, Q, P, Q)),
               w.s([w.inst(sel)], 'a1i', '( %s -> ( ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` P ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) -> ( %s ` P ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) ) )' % (A0, P, Q, P, Q, part, part, P, part, Q))], 'syld',
              '( %s -> ( P e. ( %s crect %s ) -> ( %s ` P ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) ) )' % (A0, P, Q, part, part, P, part, Q))
    ei = w.s([lop, hip, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( %s ` P ) e. ( %s [,] %s ) <-> ( ( %s ` P ) e. RR /\\ %s <_ ( %s ` P ) /\\ ( %s ` P ) <_ %s ) ) )' % (A0, part, val[0], val[1], part, val[0], part, part, val[1]))
    rw = w.s([cR(P) if part == 'Re' else cI(P), cR(Q) if part == 'Re' else cI(Q)], 'oveq12d', '( %s -> ( ( %s ` %s ) [,] ( %s ` %s ) ) = ( %s [,] %s ) )' % (A0, part, P, part, Q, val[0], val[1]))
    mem2 = w.s([mem, w.s([rw], 'eleq2d', '( %s -> ( ( %s ` P ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( %s ` P ) e. ( %s [,] %s ) ) )' % (A0, part, part, P, part, Q, part, val[0], val[1]))], 'sylibd',
               '( %s -> ( P e. ( %s crect %s ) -> ( %s ` P ) e. ( %s [,] %s ) ) )' % (A0, P, Q, part, val[0], val[1]))
    mem3 = w.s([mem2, w.s([ei], 'biimpd', '( %s -> ( ( %s ` P ) e. ( %s [,] %s ) -> ( ( %s ` P ) e. RR /\\ %s <_ ( %s ` P ) /\\ ( %s ` P ) <_ %s ) ) )' % (A0, part, val[0], val[1], part, val[0], part, part, val[1]))], 'syld',
               '( %s -> ( P e. ( %s crect %s ) -> ( ( %s ` P ) e. RR /\\ %s <_ ( %s ` P ) /\\ ( %s ` P ) <_ %s ) ) )' % (A0, P, Q, part, val[0], part, part, val[1]))
    sel2 = 'simp3' if which == 'hi' else 'simp2'
    tgt = ('( %s ` P ) <_ %s' % (part, val[1])) if which == 'hi' else ('%s <_ ( %s ` P )' % (val[0], part))
    mem4 = w.s([mem3, w.s([w.inst(sel2)], 'a1i', '( %s -> ( ( ( %s ` P ) e. RR /\\ %s <_ ( %s ` P ) /\\ ( %s ` P ) <_ %s ) -> %s ) )' % (A0, part, val[0], part, part, val[1], tgt))], 'syld',
               '( %s -> ( P e. ( %s crect %s ) -> %s ) )' % (A0, P, Q, tgt))
    return w.s([strict, mem4], 'mtod', '( %s -> -. P e. ( %s crect %s ) )' % (A0, P, Q))


def ordp(P, Q, leR, leI):
    g1 = w.s([leR, cR(P), cR(Q)], '3brtr4d', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, P, Q))
    g2 = w.s([leI, cI(P), cI(Q)], '3brtr4d', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, P, Q))
    return w.s([g1, g2], 'jca', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, P, Q, P, Q))


def nle(strictstep, lo, hi, part):
    return w.s([w.s([rl.get(hi, None) or pr, rl.get(lo, None) or pr, w.inst('x')], 'id', 'x')], 'id', 'y')


L1 = ('A', PT('X', IB)); MB = (PT('X', IA), PT('Y', 'S')); MM = (PT('X', 'S'), PT('Y', 'T'))
MT = (PT('X', 'T'), PT('Y', IB)); R2 = (PT('Y', IA), 'B')
n1 = w.s([w.s([pr, xr], 'ltnled', '( %s -> ( X < ( Re ` P ) <-> -. ( Re ` P ) <_ X ) )' % A0) if False else w.s([xr, pr], 'ltnled', '( %s -> ( X < ( Re ` P ) <-> -. ( Re ` P ) <_ X ) )' % A0), xp_], 'mpbid', '( %s -> -. ( Re ` P ) <_ X )' % A0)
n2 = w.s([w.s([sr, pi_], 'ltnled', '( %s -> ( S < ( Im ` P ) <-> -. ( Im ` P ) <_ S ) )' % A0), sp_], 'mpbid', '( %s -> -. ( Im ` P ) <_ S )' % A0)
n3 = w.s([w.s([pi_, tr], 'ltnled', '( %s -> ( ( Im ` P ) < T <-> -. T <_ ( Im ` P ) ) )' % A0), pt_], 'mpbid', '( %s -> -. T <_ ( Im ` P ) )' % A0)
n4 = w.s([w.s([pr, yr], 'ltnled', '( %s -> ( ( Re ` P ) < Y <-> -. Y <_ ( Re ` P ) ) )' % A0), py], 'mpbid', '( %s -> -. Y <_ ( Re ` P ) )' % A0)
ZER = []
for (P, Q), leR, leI, (loR, hiR, loI, hiI), (part, val, which, strict) in [
        (L1, leax, leaI, (lid[RA], lexB, lid[IA], lid[IB]), ('Re', (RA, 'X'), 'hi', n1)),
        (MB, xy, leas, (leax, leyB, lid[IA], lesB), ('Im', (IA, 'S'), 'hi', n2)),
        (MT, xy, letB, (leax, leyB, leaT, lid[IB]), ('Im', ('T', IB), 'lo', n3)),
        (R2, leyB, leaI, (leaY, lid[RB], lid[IA], lid[IB]), ('Re', ('Y', RB), 'lo', n4))]:
    op = ordp(P, Q, leR, leI)
    ic2 = incl(P, Q, loR, hiR, loI, hiI)
    lop = rl.get(val[0], None) or (ar if val[0] == RA else (ai if val[0] == IA else None))
    hip = rl.get(val[1], None) or (br if val[1] == RB else (bi if val[1] == IB else None))
    ni = notin(P, Q, part, val, None, lop, hip, strict, which)
    ZER.append(w.s([w.s([fcn, dvs], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) ) )' % A0),
                    w.s([w.s([CCS[P], CCS[Q]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, P, Q)), op, w.s([ic2, ni], 'jca', '( %s -> ( ( %s crect %s ) C_ ( A crect B ) /\\ -. P e. ( %s crect %s ) ) )' % (A0, P, Q, P, Q))], '3jca',
                        '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( ( %s crect %s ) C_ ( A crect B ) /\\ -. P e. ( %s crect %s ) ) )' % (A0, P, Q, P, Q, P, Q, P, Q, P, Q) + ' )')], 'jca',
                   '( %s -> ( ( F e. ( D -cn-> CC ) /\\ ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( ( %s crect %s ) C_ ( A crect B ) /\\ -. P e. ( %s crect %s ) ) ) ) )' % (A0, P, Q, P, Q, P, Q, P, Q, P, Q)))
# the grid decomposition
aB = w.s([ar, xr, br, ax, xB], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))
leab = w.s([ar, br, aB], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB))
psx = w.s([ab, w.s([leab, leaI], 'jca', '( %s -> %s )' % (A0, GEO)), w.s([fcn, rssd], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
def RIx(P, Q): return '( F rectint <. %s , %s >. )' % (P, Q)
grid = w.s([psx, gx, gy, w.inst('rectintgrid')], 'syl3anc',
           '( %s -> %s = ( %s + ( ( %s + ( %s + %s ) ) + %s ) ) )' % (A0, RIx('A', 'B'), RIx(*L1), RIx(*MB), RIx(*MM), RIx(*MT), RIx(*R2)))
zsub = w.s([ZER[0], w.inst('rectintgnz')], 'syl', '( %s -> %s = 0 )' % (A0, RIx(*L1)))
zmb = w.s([ZER[1], w.inst('rectintgnz')], 'syl', '( %s -> %s = 0 )' % (A0, RIx(*MB)))
zmt = w.s([ZER[2], w.inst('rectintgnz')], 'syl', '( %s -> %s = 0 )' % (A0, RIx(*MT)))
zr2 = w.s([ZER[3], w.inst('rectintgnz')], 'syl', '( %s -> %s = 0 )' % (A0, RIx(*R2)))
# the middle piece
incMM = incl(MM[0], MM[1], leax, leyB, leas, letB)
ordMM = ordp(MM[0], MM[1], xy, st)
ssMM = w.s([incMM, rssd], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A0, MM[0], MM[1]))
pdd = w.s([rssd, w.s([w.s([ab, w.s([leab, leaI], 'jca', '( %s -> %s )' % (A0, GEO))], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO)), w.s([w.s([xp_, py], 'jca', 'x')], 'id', 'y')], 'id', 'z')], 'id', 'q')
w.lines.pop(); w.lines.pop(); w.lines.pop(); w.lines.pop()
# P is in the middle piece
pxi = w.s([w.s([xr, yr, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` P ) e. ( X [,] Y ) <-> ( ( Re ` P ) e. RR /\\ X <_ ( Re ` P ) /\\ ( Re ` P ) <_ Y ) ) )' % A0),
            w.s([pr, w.s([xr, pr, xp_], 'ltled', '( %s -> X <_ ( Re ` P ) )' % A0), w.s([pr, yr, py], 'ltled', '( %s -> ( Re ` P ) <_ Y )' % A0)], '3jca', '( %s -> ( ( Re ` P ) e. RR /\\ X <_ ( Re ` P ) /\\ ( Re ` P ) <_ Y ) )' % A0)], 'mpbird',
           '( %s -> ( Re ` P ) e. ( X [,] Y ) )' % A0)
pyi = w.s([w.s([sr, tr, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Im ` P ) e. ( S [,] T ) <-> ( ( Im ` P ) e. RR /\\ S <_ ( Im ` P ) /\\ ( Im ` P ) <_ T ) ) )' % A0),
            w.s([pi_, w.s([sr, pi_, sp_], 'ltled', '( %s -> S <_ ( Im ` P ) )' % A0), w.s([pi_, tr, pt_], 'ltled', '( %s -> ( Im ` P ) <_ T )' % A0)], '3jca', '( %s -> ( ( Im ` P ) e. RR /\\ S <_ ( Im ` P ) /\\ ( Im ` P ) <_ T ) )' % A0)], 'mpbird',
           '( %s -> ( Im ` P ) e. ( S [,] T ) )' % A0)
pMM = w.s([w.s([w.s([CCS[MM[0]], CCS[MM[1]]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, MM[0], MM[1])), w.inst('elcrect')], 'syl',
                '( %s -> ( P e. ( %s crect %s ) <-> ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` P ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A0, MM[0], MM[1], MM[0], MM[1], MM[0], MM[1])),
           w.s([pc, w.s([pxi, w.s([cR(MM[0]), cR(MM[1])], 'oveq12d', '( %s -> ( ( Re ` %s ) [,] ( Re ` %s ) ) = ( X [,] Y ) )' % (A0, MM[0], MM[1]))], 'eleqtrrd', '( %s -> ( Re ` P ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A0, MM[0], MM[1])),
                w.s([pyi, w.s([cI(MM[0]), cI(MM[1])], 'oveq12d', '( %s -> ( ( Im ` %s ) [,] ( Im ` %s ) ) = ( S [,] T ) )' % (A0, MM[0], MM[1]))], 'eleqtrrd', '( %s -> ( Im ` P ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A0, MM[0], MM[1]))], '3jca',
               '( %s -> ( P e. CC /\\ ( Re ` P ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` P ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (A0, MM[0], MM[1], MM[0], MM[1]))], 'mpbird',
          '( %s -> P e. ( %s crect %s ) )' % (A0, MM[0], MM[1]))
pdD = w.s([ssMM, pMM], 'sseldd', '( %s -> P e. D )' % A0)
DMU = '( ( ( Re ` %s ) - ( Re ` %s ) ) + ( ( Im ` %s ) - ( Im ` %s ) ) )' % (MM[1], MM[0], MM[1], MM[0])
dmeq = w.s([w.s([cR(MM[1]), cR(MM[0])], 'oveq12d', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) = ( Y - X ) )' % (A0, MM[1], MM[0])),
            w.s([cI(MM[1]), cI(MM[0])], 'oveq12d', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) = ( T - S ) )' % (A0, MM[1], MM[0]))], 'oveq12d', '( %s -> %s = %s )' % (A0, DMU, DMG))
dqu = w.s([dmeq, dq], 'eqbrtrd', '( %s -> %s < Q )' % (A0, DMU))
KP2 = '( ( abs ` ( F ` P ) ) + 1 )'
mbi = w.s([], 'rectintmb', '( ( ( F e. ( D -cn-> CC ) /\\ P e. D ) /\\ ( Q e. RR+ /\\ %s ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( ( %s crect %s ) C_ D /\\ P e. ( %s crect %s ) /\\ %s < Q ) ) ) -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )'
          % (CNA2, MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], DMU, RIx(*MM), KP2, DMU))
mb = w.s([w.s([w.s([fcn, pdD], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D ) )' % A0),
               w.s([qrp, cna], 'jca', '( %s -> ( Q e. RR+ /\\ %s ) )' % (A0, CNA2)),
               w.s([w.s([CCS[MM[0]], CCS[MM[1]]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, MM[0], MM[1])), ordMM, w.s([ssMM, pMM, dqu], '3jca', '( %s -> ( ( %s crect %s ) C_ D /\\ P e. ( %s crect %s ) /\\ %s < Q ) )' % (A0, MM[0], MM[1], MM[0], MM[1], DMU))], '3jca',
                   '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( ( %s crect %s ) C_ D /\\ P e. ( %s crect %s ) /\\ %s < Q ) )' % (A0, MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], DMU) + ' )')], '3jca',
              '( %s -> ( ( F e. ( D -cn-> CC ) /\\ P e. D ) /\\ ( Q e. RR+ /\\ %s ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( ( %s crect %s ) C_ D /\\ P e. ( %s crect %s ) /\\ %s < Q ) ) ) )' % (A0, CNA2, MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], MM[0], MM[1], DMU)), mbi], 'syl',
         '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (A0, RIx(*MM), KP2, DMU))
# collapse the decomposition
mmcl = w.s([w.s([CCS[MM[0]], CCS[MM[1]]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, MM[0], MM[1])), ordMM, w.s([fcn, ssMM], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (A0, MM[0], MM[1]))], '3jca', '( %s -> %s )' % (A0, PSOF(MM[0], MM[1])))
icl = w.s([mmcl, w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A0, RIx(*MM)))
c1 = w.s([w.s([zmb], 'oveq1d', '( %s -> ( %s + ( %s + %s ) ) = ( 0 + ( %s + 0 ) ) )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*MM))) if False else w.s([zmb, w.s([zmt], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + 0 ) )' % (A0, RIx(*MM), RIx(*MT), RIx(*MM)))], 'oveq12d',
            '( %s -> ( %s + ( %s + %s ) ) = ( 0 + ( %s + 0 ) ) )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*MM)))], 'id', 'x')
w.lines.pop()
c1 = w.s([zmb, w.s([zmt], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + 0 ) )' % (A0, RIx(*MM), RIx(*MT), RIx(*MM)))], 'oveq12d',
         '( %s -> ( %s + ( %s + %s ) ) = ( 0 + ( %s + 0 ) ) )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*MM)))
c2 = w.s([w.s([icl], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A0, RIx(*MM), RIx(*MM)))], 'oveq2d', '( %s -> ( 0 + ( %s + 0 ) ) = ( 0 + %s ) )' % (A0, RIx(*MM), RIx(*MM)))
c3 = w.s([icl], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A0, RIx(*MM), RIx(*MM)))
cmid = w.s([w.s([c1, c2], 'eqtrd', '( %s -> ( %s + ( %s + %s ) ) = ( 0 + %s ) )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*MM))), c3], 'eqtrd',
           '( %s -> ( %s + ( %s + %s ) ) = %s )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*MM)))
d1 = w.s([cmid, zr2], 'oveq12d', '( %s -> ( ( %s + ( %s + %s ) ) + %s ) = ( %s + 0 ) )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*R2), RIx(*MM)))
d2 = w.s([d1, w.s([icl], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A0, RIx(*MM), RIx(*MM)))], 'eqtrd', '( %s -> ( ( %s + ( %s + %s ) ) + %s ) = %s )' % (A0, RIx(*MB), RIx(*MM), RIx(*MT), RIx(*R2), RIx(*MM)))
d3 = w.s([zsub, d2], 'oveq12d', '( %s -> ( %s + ( ( %s + ( %s + %s ) ) + %s ) ) = ( 0 + %s ) )' % (A0, RIx(*L1), RIx(*MB), RIx(*MM), RIx(*MT), RIx(*R2), RIx(*MM)))
d4 = w.s([d3, c3], 'eqtrd', '( %s -> ( %s + ( ( %s + ( %s + %s ) ) + %s ) ) = %s )' % (A0, RIx(*L1), RIx(*MB), RIx(*MM), RIx(*MT), RIx(*R2), RIx(*MM)))
tot = w.s([grid, d4], 'eqtrd', '( %s -> %s = %s )' % (A0, RIx('A', 'B'), RIx(*MM)))
w.qed([w.s([tot], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, RIx('A', 'B'), RIx(*MM))),
       w.s([mb, w.s([dmeq], 'oveq2d', '( %s -> ( ( 2 x. %s ) x. %s ) = ( ( 2 x. %s ) x. %s ) )' % (A0, KP2, DMU, KP2, DMG))], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (A0, RIx(*MM), KP2, DMG))], 'eqbrtrd',
      '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (A0, RIx('A', 'B'), KP2, DMG))
run(w)

# ---- rectintgour1: Cauchy-Goursat off one point
INT = '( ( %s < ( Re ` P ) /\\ ( Re ` P ) < %s ) /\\ ( %s < ( Im ` P ) /\\ ( Im ` P ) < %s ) )' % (RA, RB, IA, IB)
A0 = '( %s /\\ ( P e. CC /\\ %s ) /\\ %s )' % (AB, INT, HOL1)
IABx = '( F rectint <. A , B >. )'
w = W('rectintgour1', 'Cauchy-Goursat off one point: the boundary integral vanishes for a function continuous on the domain and differentiable on the closed rectangle except at one interior point.')
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pin = w.s([], 'simp2', '( %s -> ( P e. CC /\\ %s ) )' % (A0, INT))
pc = w.s([pin, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
itv = w.s([pin, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, INT))
hol = w.s([], 'simp3', '( %s -> %s )' % (A0, HOL1))
fcn = w.s([hol, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rssd = w.s([hol, w.inst('simp2')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
dvs = w.s([hol, w.inst('simp3')], 'syl', '( %s -> ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) )' % A0)
i1 = w.s([itv, w.inst('simpl')], 'syl', '( %s -> ( %s < ( Re ` P ) /\\ ( Re ` P ) < %s ) )' % (A0, RA, RB))
i2 = w.s([itv, w.inst('simpr')], 'syl', '( %s -> ( %s < ( Im ` P ) /\\ ( Im ` P ) < %s ) )' % (A0, IA, IB))
aP = w.s([i1, w.inst('simpl')], 'syl', '( %s -> %s < ( Re ` P ) )' % (A0, RA))
Pb = w.s([i1, w.inst('simpr')], 'syl', '( %s -> ( Re ` P ) < %s )' % (A0, RB))
cP = w.s([i2, w.inst('simpl')], 'syl', '( %s -> %s < ( Im ` P ) )' % (A0, IA))
Pd = w.s([i2, w.inst('simpr')], 'syl', '( %s -> ( Im ` P ) < %s )' % (A0, IB))
ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc, w.inst('recl')], 'syl', '( %s -> ( Re ` P ) e. RR )' % A0)
pi_ = w.s([pc, w.inst('imcl')], 'syl', '( %s -> ( Im ` P ) e. RR )' % A0)
DA = '( ( Re ` P ) - %s )' % RA; DB = '( %s - ( Re ` P ) )' % RB
DC = '( ( Im ` P ) - %s )' % IA; DE = '( %s - ( Im ` P ) )' % IB
dists = []
for nm, hi, lo, hir, lor, lt in [(DA, '( Re ` P )', RA, pr, ar, aP), (DB, RB, '( Re ` P )', br, pr, Pb),
                                 (DC, '( Im ` P )', IA, pi_, ai, cP), (DE, IB, '( Im ` P )', bi, pi_, Pd)]:
    rr = w.s([hir, lor], 'resubcld', '( %s -> %s e. RR )' % (A0, nm))
    gg = w.s([w.s([lor, hir], 'posdifd', '( %s -> ( %s < %s <-> 0 < %s ) )' % (A0, lo, hi, nm)), lt], 'mpbid', '( %s -> 0 < %s )' % (A0, nm))
    dists.append((nm, rr, w.s([rr, gg], 'elrpd', '( %s -> %s e. RR+ )' % (A0, nm)), gg))
WW = '( ( %s + %s ) + ( %s + %s ) )' % (DB, DA, DE, DC)
wrp = w.s([w.s([dists[1][2], dists[0][2]], 'rpaddcld', '( %s -> ( %s + %s ) e. RR+ )' % (A0, DB, DA)),
           w.s([dists[3][2], dists[2][2]], 'rpaddcld', '( %s -> ( %s + %s ) e. RR+ )' % (A0, DE, DC))], 'rpaddcld', '( %s -> %s e. RR+ )' % (A0, WW))
# P lies in the rectangle, so ( F ` P ) is a complex number
leab = w.s([ar, br, w.s([ar, pr, br, aP, Pb], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB))
leai = w.s([ai, bi, w.s([ai, pi_, bi, cP, Pd], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))
pxi = w.s([w.s([ar, br, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` P ) e. ( %s [,] %s ) <-> ( ( Re ` P ) e. RR /\\ %s <_ ( Re ` P ) /\\ ( Re ` P ) <_ %s ) ) )' % (A0, RA, RB, RA, RB)),
           w.s([pr, w.s([ar, pr, aP], 'ltled', '( %s -> %s <_ ( Re ` P ) )' % (A0, RA)), w.s([pr, br, Pb], 'ltled', '( %s -> ( Re ` P ) <_ %s )' % (A0, RB))], '3jca',
               '( %s -> ( ( Re ` P ) e. RR /\\ %s <_ ( Re ` P ) /\\ ( Re ` P ) <_ %s ) )' % (A0, RA, RB))], 'mpbird', '( %s -> ( Re ` P ) e. ( %s [,] %s ) )' % (A0, RA, RB))
pyi = w.s([w.s([ai, bi, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Im ` P ) e. ( %s [,] %s ) <-> ( ( Im ` P ) e. RR /\\ %s <_ ( Im ` P ) /\\ ( Im ` P ) <_ %s ) ) )' % (A0, IA, IB, IA, IB)),
           w.s([pi_, w.s([ai, pi_, cP], 'ltled', '( %s -> %s <_ ( Im ` P ) )' % (A0, IA)), w.s([pi_, bi, Pd], 'ltled', '( %s -> ( Im ` P ) <_ %s )' % (A0, IB))], '3jca',
               '( %s -> ( ( Im ` P ) e. RR /\\ %s <_ ( Im ` P ) /\\ ( Im ` P ) <_ %s ) )' % (A0, IA, IB))], 'mpbird', '( %s -> ( Im ` P ) e. ( %s [,] %s ) )' % (A0, IA, IB))
pab = w.s([w.s([w.s([ac, bc], 'jca', '( %s -> %s )' % (A0, AB)), w.inst('elcrect')], 'syl', '( %s -> ( P e. ( A crect B ) <-> ( P e. CC /\\ ( Re ` P ) e. ( %s [,] %s ) /\\ ( Im ` P ) e. ( %s [,] %s ) ) ) )' % (A0, RA, RB, IA, IB)),
           w.s([pc, pxi, pyi], '3jca', '( %s -> ( P e. CC /\\ ( Re ` P ) e. ( %s [,] %s ) /\\ ( Im ` P ) e. ( %s [,] %s ) ) )' % (A0, RA, RB, IA, IB))], 'mpbird', '( %s -> P e. ( A crect B ) )' % A0)
pdd = w.s([rssd, pab], 'sseldd', '( %s -> P e. D )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fpc = w.s([ff, pdd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
KK = '( ( abs ` ( F ` P ) ) + 1 )'
kre = w.s([w.s([fpc], 'abscld', '( %s -> ( abs ` ( F ` P ) ) e. RR )' % A0), closed(w, A0, '1re', '1 e. RR')], 'readdcld', '( %s -> %s e. RR )' % (A0, KK))
kgt = w.s([w.s([fpc], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` P ) ) )' % A0), closed(w, A0, '0lt1', '0 < 1'), w.s([fpc], 'abscld', '( %s -> ( abs ` ( F ` P ) ) e. RR )' % A0), closed(w, A0, '1re', '1 e. RR')], 'addgegt0d', '( %s -> 0 < %s )' % (A0, KK))
krp = w.s([kre, kgt], 'elrpd', '( %s -> %s e. RR+ )' % (A0, KK))
# the continuity radius
cni = w.s([w.s([fcn, pdd, closed(w, A0, '1rp', '1 e. RR+')], '3jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D /\\ 1 e. RR+ ) )' % A0), w.inst('cncfi')], 'syl',
          '( %s -> E. q e. RR+ A. s e. D ( ( abs ` ( s - P ) ) < q -> ( abs ` ( ( F ` s ) - ( F ` P ) ) ) < 1 ) )' % A0)
# --- level A1: the continuity radius q
CNAq = 'A. s e. D ( ( abs ` ( s - P ) ) < q -> ( abs ` ( ( F ` s ) - ( F ` P ) ) ) < 1 )'
A1 = '( %s /\\ ( q e. RR+ /\\ %s ) )' % (A0, CNAq)
qrp = w.s([], 'simprl', '( %s -> q e. RR+ )' % A1)
cnaq = w.s([], 'simprr', '( %s -> %s )' % (A1, CNAq))
def u1(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
H2 = '( 1 / 2 )'
QW = '( q / ( 2 x. %s ) )' % WW
def SM(a, b): return '( ( %s x. %s ) / ( %s + %s ) )' % (a, b, a, b)
M1 = SM(H2, QW)
Z2 = '( x / ( ( 2 x. %s ) x. %s ) )' % (KK, WW)
RX = SM(M1, Z2)
A2 = '( %s /\\ x e. RR+ )' % A1
xrp = w.s([], 'simpr', '( %s -> x e. RR+ )' % A2)
def u2(st, f):
    return w.s([w.s([st], 'adantr', '( %s -> %s )' % (A1, f))], 'adantr', '( %s -> %s )' % (A2, f))
def u2b(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
wrp2 = u2(wrp, '%s e. RR+' % WW)
krp2 = u2(krp, '%s e. RR+' % KK)
qrp2 = u2b(qrp, 'q e. RR+')
cnaq2 = u2b(cnaq, CNAq)
h2rp = w.s([closed(w, A2, '1rp', '1 e. RR+'), closed(w, A2, '2rp', '2 e. RR+')], 'rpdivcld', '( %s -> %s e. RR+ )' % (A2, H2))
qwrp = w.s([qrp2, w.s([closed(w, A2, '2rp', '2 e. RR+'), wrp2], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A2, WW))], 'rpdivcld', '( %s -> %s e. RR+ )' % (A2, QW))
z2rp = w.s([xrp, w.s([w.s([closed(w, A2, '2rp', '2 e. RR+'), krp2], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A2, KK)), wrp2], 'rpmulcld', '( %s -> ( ( 2 x. %s ) x. %s ) e. RR+ )' % (A2, KK, WW))], 'rpdivcld', '( %s -> %s e. RR+ )' % (A2, Z2))
sm1 = w.s([w.s([h2rp, qwrp], 'jca', '( %s -> ( %s e. RR+ /\\ %s e. RR+ ) )' % (A2, H2, QW)), w.inst('softmin')], 'syl', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ %s ) ) )' % (A2, M1, M1, H2, M1, QW))
m1rp = w.s([sm1, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A2, M1))
m1h = w.s([w.s([sm1, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A2, M1, H2, M1, QW)), w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A2, M1, H2))
m1q = w.s([w.s([sm1, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A2, M1, H2, M1, QW)), w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A2, M1, QW))
sm2 = w.s([w.s([m1rp, z2rp], 'jca', '( %s -> ( %s e. RR+ /\\ %s e. RR+ ) )' % (A2, M1, Z2)), w.inst('softmin')], 'syl', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ %s ) ) )' % (A2, RX, RX, M1, RX, Z2))
rrp = w.s([sm2, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A2, RX))
rm1 = w.s([w.s([sm2, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A2, RX, M1, RX, Z2)), w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A2, RX, M1))
rz2 = w.s([w.s([sm2, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A2, RX, M1, RX, Z2)), w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A2, RX, Z2))
rre = w.s([rrp, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, RX))
h2re = closed(w, A2, 'halfre', '( 1 / 2 ) e. RR')
qwre = w.s([qwrp, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, QW))
z2re = w.s([z2rp, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, Z2))
m1re = w.s([m1rp, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, M1))
rh2 = w.s([rre, m1re, h2re, rm1, m1h], 'letrd', '( %s -> %s <_ %s )' % (A2, RX, H2))
rqw = w.s([rre, m1re, qwre, rm1, m1q], 'letrd', '( %s -> %s <_ %s )' % (A2, RX, QW))
rlt1 = w.s([rre, h2re, closed(w, A2, '1re', '1 e. RR'), rh2, closed(w, A2, 'halflt1', '( 1 / 2 ) < 1')], 'lelttrd', '( %s -> %s < 1 )' % (A2, RX))
# --- the four cut coordinates and the twelve grid inequalities
D2 = {}
for nm, rr, rp, gg in dists:
    D2[nm] = (u2(rr, '%s e. RR' % nm), u2(rp, '%s e. RR+' % nm), u2(gg, '0 < %s' % nm))
pr2 = u2(pr, '( Re ` P ) e. RR'); pi2 = u2(pi_, '( Im ` P ) e. RR')
ar2 = u2(ar, '%s e. RR' % RA); br2 = u2(br, '%s e. RR' % RB)
ai2 = u2(ai, '%s e. RR' % IA); bi2 = u2(bi, '%s e. RR' % IB)
pc2 = u2(pc, 'P e. CC'); ac2 = u2(ac, 'A e. CC'); bc2 = u2(bc, 'B e. CC')
fcn2 = u2(fcn, 'F e. ( D -cn-> CC )')
rss2 = u2(rssd, '( A crect B ) C_ D'); dvs2 = u2(dvs, '( ( A crect B ) \\ { P } ) C_ dom ( CC _D F )')
RES = {}
for tag, dlo, dhi, lov, hiv, lor, hir, pv, pvr in [('re', DA, DB, RA, RB, ar2, br2, '( Re ` P )', pr2),
                                                  ('im', DC, DE, IA, IB, ai2, bi2, '( Im ` P )', pi2)]:
    rdl = '( %s x. %s )' % (RX, dlo); rdh = '( %s x. %s )' % (RX, dhi)
    rdlrp = w.s([rrp, D2[dlo][1]], 'rpmulcld', '( %s -> %s e. RR+ )' % (A2, rdl))
    rdhrp = w.s([rrp, D2[dhi][1]], 'rpmulcld', '( %s -> %s e. RR+ )' % (A2, rdh))
    rdlr = w.s([rdlrp, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, rdl))
    rdhr = w.s([rdhrp, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, rdh))
    rdlg = w.s([rdlrp, w.inst('rpgt0')], 'syl', '( %s -> 0 < %s )' % (A2, rdl))
    rdhg = w.s([rdhrp, w.inst('rpgt0')], 'syl', '( %s -> 0 < %s )' % (A2, rdh))
    rdlge = w.s([rdlrp, w.inst('rpge0')], 'syl', '( %s -> 0 <_ %s )' % (A2, rdl))
    rdhge = w.s([rdhrp, w.inst('rpge0')], 'syl', '( %s -> 0 <_ %s )' % (A2, rdh))
    ltl = w.s([w.s([rre, closed(w, A2, '1re', '1 e. RR'), D2[dlo][1]], 'ltmul1d', '( %s -> ( %s < 1 <-> %s < ( 1 x. %s ) ) )' % (A2, RX, rdl, dlo)), rlt1], 'mpbid', '( %s -> %s < ( 1 x. %s ) )' % (A2, rdl, dlo))
    ltl2 = w.s([ltl, w.s([w.s([D2[dlo][0]], 'recnd', '( %s -> %s e. CC )' % (A2, dlo))], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A2, dlo, dlo))], 'breqtrd', '( %s -> %s < %s )' % (A2, rdl, dlo))
    lth = w.s([w.s([rre, closed(w, A2, '1re', '1 e. RR'), D2[dhi][1]], 'ltmul1d', '( %s -> ( %s < 1 <-> %s < ( 1 x. %s ) ) )' % (A2, RX, rdh, dhi)), rlt1], 'mpbid', '( %s -> %s < ( 1 x. %s ) )' % (A2, rdh, dhi))
    lth2 = w.s([lth, w.s([w.s([D2[dhi][0]], 'recnd', '( %s -> %s e. CC )' % (A2, dhi))], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A2, dhi, dhi))], 'breqtrd', '( %s -> %s < %s )' % (A2, rdh, dhi))
    XX = '( %s - %s )' % (pv, rdl); YY = '( %s + %s )' % (pv, rdh)
    xre = w.s([pvr, rdlr], 'resubcld', '( %s -> %s e. RR )' % (A2, XX))
    yre = w.s([pvr, rdhr], 'readdcld', '( %s -> %s e. RR )' % (A2, YY))
    nnc = w.s([w.s([pvr], 'recnd', '( %s -> %s e. CC )' % (A2, pv)), w.s([lor], 'recnd', '( %s -> %s e. CC )' % (A2, lov))], 'nncand', '( %s -> ( %s - %s ) = %s )' % (A2, pv, dlo, lov))
    lowlt = w.s([w.s([nnc], 'eqcomd', '( %s -> %s = ( %s - %s ) )' % (A2, lov, pv, dlo)), w.s([rdlr, D2[dlo][0], pvr, ltl2], 'ltsub2dd', '( %s -> ( %s - %s ) < %s )' % (A2, pv, dlo, XX))], 'eqbrtrd', '( %s -> %s < %s )' % (A2, lov, XX))
    pnc = w.s([w.s([pvr], 'recnd', '( %s -> %s e. CC )' % (A2, pv)), w.s([hir], 'recnd', '( %s -> %s e. CC )' % (A2, hiv)), w.inst('pncan3')], 'syl2anc', '( %s -> ( %s + %s ) = %s )' % (A2, pv, dhi, hiv))
    hilt = w.s([w.s([rdhr, D2[dhi][0], pvr, lth2], 'ltadd2dd', '( %s -> %s < ( %s + %s ) )' % (A2, YY, pv, dhi)), pnc], 'breqtrd', '( %s -> %s < %s )' % (A2, YY, hiv))
    z0r = closed(w, A2, '0re', '0 e. RR')
    xlep = w.s([w.s([z0r, rdlr, pvr, rdlge], 'lesub2dd', '( %s -> %s <_ ( %s - 0 ) )' % (A2, XX, pv)), w.s([w.s([pvr], 'recnd', '( %s -> %s e. CC )' % (A2, pv))], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A2, pv, pv))], 'breqtrd', '( %s -> %s <_ %s )' % (A2, XX, pv))
    xltp = w.s([w.s([z0r, rdlr, pvr, rdlg], 'ltsub2dd', '( %s -> %s < ( %s - 0 ) )' % (A2, XX, pv)), w.s([w.s([pvr], 'recnd', '( %s -> %s e. CC )' % (A2, pv))], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A2, pv, pv))], 'breqtrd', '( %s -> %s < %s )' % (A2, XX, pv))
    pley = w.s([w.s([pvr, rdhr], 'addge01d', '( %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (A2, rdh, pv, YY)), rdhge], 'mpbid', '( %s -> %s <_ %s )' % (A2, pv, YY))
    plty = w.s([w.s([rdhr, pvr], 'ltaddposd', '( %s -> ( 0 < %s <-> %s < %s ) )' % (A2, rdh, pv, YY)), rdhg], 'mpbid', '( %s -> %s < %s )' % (A2, pv, YY))
    xley = w.s([xre, pvr, yre, xlep, pley], 'letrd', '( %s -> %s <_ %s )' % (A2, XX, YY))
    dif = w.s([w.s([pvr], 'recnd', '( %s -> %s e. CC )' % (A2, pv)), w.s([rdhr], 'recnd', '( %s -> %s e. CC )' % (A2, rdh)), w.s([rdlr], 'recnd', '( %s -> %s e. CC )' % (A2, rdl))], 'pnncand', '( %s -> ( %s - %s ) = ( %s + %s ) )' % (A2, YY, XX, rdh, rdl))
    dist = w.s([w.s([w.s([rre], 'recnd', '( %s -> %s e. CC )' % (A2, RX)), w.s([D2[dhi][0]], 'recnd', '( %s -> %s e. CC )' % (A2, dhi)), w.s([D2[dlo][0]], 'recnd', '( %s -> %s e. CC )' % (A2, dlo))], 'adddid', '( %s -> ( %s x. ( %s + %s ) ) = ( %s + %s ) )' % (A2, RX, dhi, dlo, rdh, rdl))], 'eqcomd',
               '( %s -> ( %s + %s ) = ( %s x. ( %s + %s ) ) )' % (A2, rdh, rdl, RX, dhi, dlo))
    RES[tag] = dict(X=XX, Y=YY, xre=xre, yre=yre, lowlt=lowlt, hilt=hilt, xley=xley, xltp=xltp, plty=plty,
                    diff=w.s([dif, dist], 'eqtrd', '( %s -> ( %s - %s ) = ( %s x. ( %s + %s ) ) )' % (A2, YY, XX, RX, dhi, dlo)))
# --- the two analytic bounds and the conclusion
XR = RES['re']['X']; YR = RES['re']['Y']; SI = RES['im']['X']; TI2 = RES['im']['Y']
DMI = '( ( %s - %s ) + ( %s - %s ) )' % (YR, XR, TI2, SI)
rwc = w.s([rre], 'recnd', '( %s -> %s e. CC )' % (A2, RX))
wre = w.s([wrp2, w.inst('rpre')], 'syl', '( %s -> %s e. RR )' % (A2, WW))
wcc = w.s([wre], 'recnd', '( %s -> %s e. CC )' % (A2, WW))
wge = w.s([wrp2, w.inst('rpge0')], 'syl', '( %s -> 0 <_ %s )' % (A2, WW))
dsum = w.s([w.s([RES['re']['diff'], RES['im']['diff']], 'oveq12d', '( %s -> %s = ( ( %s x. ( %s + %s ) ) + ( %s x. ( %s + %s ) ) ) )' % (A2, DMI, RX, DB, DA, RX, DE, DC)),
            w.s([w.s([rwc, w.s([w.s([D2[DB][0]], 'recnd', '( %s -> %s e. CC )' % (A2, DB)), w.s([D2[DA][0]], 'recnd', '( %s -> %s e. CC )' % (A2, DA))], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A2, DB, DA)),
                          w.s([w.s([D2[DE][0]], 'recnd', '( %s -> %s e. CC )' % (A2, DE)), w.s([D2[DC][0]], 'recnd', '( %s -> %s e. CC )' % (A2, DC))], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A2, DE, DC))], 'adddid',
                         '( %s -> ( %s x. %s ) = ( ( %s x. ( %s + %s ) ) + ( %s x. ( %s + %s ) ) ) )' % (A2, RX, WW, RX, DB, DA, RX, DE, DC))], 'eqcomd',
                '( %s -> ( ( %s x. ( %s + %s ) ) + ( %s x. ( %s + %s ) ) ) = ( %s x. %s ) )' % (A2, RX, DB, DA, RX, DE, DC, RX, WW))], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A2, DMI, RX, WW))
rwr = w.s([rre, wre], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A2, RX, WW))
qwwr = w.s([qwre, wre], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A2, QW, WW))
m2w = w.s([closed(w, A2, '2rp', '2 e. RR+'), wrp2], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A2, WW))
dcq = w.s([w.s([qrp2, w.inst('rpcn')], 'syl', '( %s -> q e. CC )' % A2), w.s([m2w, w.inst('rpcn')], 'syl', '( %s -> ( 2 x. %s ) e. CC )' % (A2, WW)), w.s([m2w, w.inst('rpne0')], 'syl', '( %s -> ( 2 x. %s ) =/= 0 )' % (A2, WW))], 'divcan2d',
          '( %s -> ( ( 2 x. %s ) x. %s ) = q )' % (A2, WW, QW))
qwc = w.s([qwre], 'recnd', '( %s -> %s e. CC )' % (A2, QW))
t2c = closed(w, A2, '2cn', '2 e. CC')
as1 = w.s([t2c, wcc, qwc], 'mulassd', '( %s -> ( ( 2 x. %s ) x. %s ) = ( 2 x. ( %s x. %s ) ) )' % (A2, WW, QW, WW, QW))
cm1 = w.s([wcc, qwc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A2, WW, QW, QW, WW))
e2a = w.s([w.s([as1], 'eqcomd', '( %s -> ( 2 x. ( %s x. %s ) ) = ( ( 2 x. %s ) x. %s ) )' % (A2, WW, QW, WW, QW)), dcq], 'eqtrd', '( %s -> ( 2 x. ( %s x. %s ) ) = q )' % (A2, WW, QW))
e2b = w.s([w.s([cm1], 'oveq2d', '( %s -> ( 2 x. ( %s x. %s ) ) = ( 2 x. ( %s x. %s ) ) )' % (A2, WW, QW, QW, WW))], 'eqcomd', '( %s -> ( 2 x. ( %s x. %s ) ) = ( 2 x. ( %s x. %s ) ) )' % (A2, QW, WW, WW, QW))
e2c = w.s([e2b, e2a], 'eqtrd', '( %s -> ( 2 x. ( %s x. %s ) ) = q )' % (A2, QW, WW))
dmb = w.s([e2c, w.s([w.s([qrp2, w.inst('rpcn')], 'syl', '( %s -> q e. CC )' % A2), w.s([qwwr], 'recnd', '( %s -> ( %s x. %s ) e. CC )' % (A2, QW, WW)), w.s([t2c, closed(w, A2, '2ne0', '2 =/= 0')], 'jca', '( %s -> ( 2 e. CC /\\ 2 =/= 0 ) )' % A2), w.inst('divmul')], 'syl3anc',
                '( %s -> ( ( q / 2 ) = ( %s x. %s ) <-> ( 2 x. ( %s x. %s ) ) = q ) )' % (A2, QW, WW, QW, WW))], 'mpbird', '( %s -> ( q / 2 ) = ( %s x. %s ) )' % (A2, QW, WW))
mul1 = w.s([w.s([rre, qwre, w.s([wre, wge], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A2, WW, WW))], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A2, RX, QW, WW, WW)), rqw, w.inst('lemul1a')], 'syl2anc',
           '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A2, RX, WW, QW, WW))
qre2 = w.s([qrp2, w.inst('rpre')], 'syl', '( %s -> q e. RR )' % A2)
rwlt = w.s([rwr, qwwr, qre2, mul1, w.s([w.s([dmb], 'eqcomd', '( %s -> ( %s x. %s ) = ( q / 2 ) )' % (A2, QW, WW)), w.s([qrp2, w.inst('rphalflt')], 'syl', '( %s -> ( q / 2 ) < q )' % A2)], 'eqbrtrd', '( %s -> ( %s x. %s ) < q )' % (A2, QW, WW))], 'lelttrd',
           '( %s -> ( %s x. %s ) < q )' % (A2, RX, WW))
dmlt = w.s([dsum, rwlt], 'eqbrtrd', '( %s -> %s < q )' % (A2, DMI))
# apply rectintg1a
GXI = '( ( %s e. RR /\\ %s e. RR ) /\\ ( %s < %s /\\ %s <_ %s /\\ %s < %s ) )' % (XR, YR, RA, XR, XR, YR, YR, RB)
GYI = '( ( %s e. RR /\\ %s e. RR ) /\\ ( %s < %s /\\ %s <_ %s /\\ %s < %s ) )' % (SI, TI2, IA, SI, SI, TI2, TI2, IB)
MIDI = '( ( %s < ( Re ` P ) /\\ ( Re ` P ) < %s ) /\\ ( %s < ( Im ` P ) /\\ ( Im ` P ) < %s ) )' % (XR, YR, SI, TI2)
CQI = '( q e. RR+ /\\ %s < q /\\ %s )' % (DMI, CNAq)
g1i = w.s([], 'rectintg1a', '( ( ( %s /\\ ( P e. CC /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (AB, HOL1, GXI, GYI, MIDI, CQI, IABx, KK, DMI))
holc = w.s([fcn2, rss2, dvs2], '3jca', '( %s -> %s )' % (A2, HOL1))
h1 = w.s([w.s([ac2, bc2], 'jca', '( %s -> %s )' % (A2, AB)), w.s([pc2, holc], 'jca', '( %s -> ( P e. CC /\\ %s ) )' % (A2, HOL1))], 'jca', '( %s -> ( %s /\\ ( P e. CC /\\ %s ) ) )' % (A2, AB, HOL1))
gxs = w.s([w.s([RES['re']['xre'], RES['re']['yre']], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (A2, XR, YR)),
           w.s([RES['re']['lowlt'], RES['re']['xley'], RES['re']['hilt']], '3jca', '( %s -> ( %s < %s /\\ %s <_ %s /\\ %s < %s ) )' % (A2, RA, XR, XR, YR, YR, RB))], 'jca', '( %s -> %s )' % (A2, GXI))
gys = w.s([w.s([RES['im']['xre'], RES['im']['yre']], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (A2, SI, TI2)),
           w.s([RES['im']['lowlt'], RES['im']['xley'], RES['im']['hilt']], '3jca', '( %s -> ( %s < %s /\\ %s <_ %s /\\ %s < %s ) )' % (A2, IA, SI, SI, TI2, TI2, IB))], 'jca', '( %s -> %s )' % (A2, GYI))
mids = w.s([w.s([RES['re']['xltp'], RES['re']['plty']], 'jca', '( %s -> ( %s < ( Re ` P ) /\\ ( Re ` P ) < %s ) )' % (A2, XR, YR)),
            w.s([RES['im']['xltp'], RES['im']['plty']], 'jca', '( %s -> ( %s < ( Im ` P ) /\\ ( Im ` P ) < %s ) )' % (A2, SI, TI2))], 'jca', '( %s -> %s )' % (A2, MIDI))
cqs = w.s([qrp2, dmlt, cnaq2], '3jca', '( %s -> %s )' % (A2, CQI))
bnd = w.s([w.s([h1, w.s([gxs, gys], 'jca', '( %s -> ( %s /\\ %s ) )' % (A2, GXI, GYI)), w.s([mids, cqs], 'jca', '( %s -> ( %s /\\ %s ) )' % (A2, MIDI, CQI))], '3jca',
                '( %s -> ( ( %s /\\ ( P e. CC /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (A2, AB, HOL1, GXI, GYI, MIDI, CQI)), g1i], 'syl',
          '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (A2, IABx, KK, DMI))
# the bound is at most x
m2k = w.s([closed(w, A2, '2rp', '2 e. RR+'), krp2], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A2, KK))
m2kr = w.s([m2k, w.inst('rpre')], 'syl', '( %s -> ( 2 x. %s ) e. RR )' % (A2, KK))
m2kg = w.s([m2k, w.inst('rpge0')], 'syl', '( %s -> 0 <_ ( 2 x. %s ) )' % (A2, KK))
z2w = w.s([z2re, wre], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A2, Z2, WW))
mu1 = w.s([w.s([rre, z2re, w.s([wre, wge], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A2, WW, WW))], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A2, RX, Z2, WW, WW)), rz2, w.inst('lemul1a')], 'syl2anc',
          '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A2, RX, WW, Z2, WW))
mu2 = w.s([w.s([rwr, z2w, w.s([m2kr, m2kg], 'jca', '( %s -> ( ( 2 x. %s ) e. RR /\\ 0 <_ ( 2 x. %s ) ) )' % (A2, KK, KK))], '3jca', '( %s -> ( ( %s x. %s ) e. RR /\\ ( %s x. %s ) e. RR /\\ ( ( 2 x. %s ) e. RR /\\ 0 <_ ( 2 x. %s ) ) ) )' % (A2, RX, WW, Z2, WW, KK, KK)), mu1, w.inst('lemul2a')], 'syl2anc',
          '( %s -> ( ( 2 x. %s ) x. ( %s x. %s ) ) <_ ( ( 2 x. %s ) x. ( %s x. %s ) ) )' % (A2, KK, RX, WW, KK, Z2, WW))
z2c = w.s([z2re], 'recnd', '( %s -> %s e. CC )' % (A2, Z2))
m2kc = w.s([m2kr], 'recnd', '( %s -> ( 2 x. %s ) e. CC )' % (A2, KK))
mkw = w.s([m2k, wrp2], 'rpmulcld', '( %s -> ( ( 2 x. %s ) x. %s ) e. RR+ )' % (A2, KK, WW))
ex_ = w.s([w.s([w.s([z2c, wcc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A2, Z2, WW, WW, Z2))], 'oveq2d', '( %s -> ( ( 2 x. %s ) x. ( %s x. %s ) ) = ( ( 2 x. %s ) x. ( %s x. %s ) ) )' % (A2, KK, Z2, WW, KK, WW, Z2)),
            w.s([w.s([m2kc, wcc, z2c], 'mulassd', '( %s -> ( ( ( 2 x. %s ) x. %s ) x. %s ) = ( ( 2 x. %s ) x. ( %s x. %s ) ) )' % (A2, KK, WW, Z2, KK, WW, Z2))], 'eqcomd', '( %s -> ( ( 2 x. %s ) x. ( %s x. %s ) ) = ( ( ( 2 x. %s ) x. %s ) x. %s ) )' % (A2, KK, WW, Z2, KK, WW, Z2))], 'eqtrd',
           '( %s -> ( ( 2 x. %s ) x. ( %s x. %s ) ) = ( ( ( 2 x. %s ) x. %s ) x. %s ) )' % (A2, KK, Z2, WW, KK, WW, Z2))
dcx = w.s([w.s([xrp, w.inst('rpcn')], 'syl', '( %s -> x e. CC )' % A2), w.s([mkw, w.inst('rpcn')], 'syl', '( %s -> ( ( 2 x. %s ) x. %s ) e. CC )' % (A2, KK, WW)), w.s([mkw, w.inst('rpne0')], 'syl', '( %s -> ( ( 2 x. %s ) x. %s ) =/= 0 )' % (A2, KK, WW))], 'divcan2d',
          '( %s -> ( ( ( 2 x. %s ) x. %s ) x. %s ) = x )' % (A2, KK, WW, Z2))
iabr = w.s([w.s([w.s([ac2, bc2], 'jca', '( %s -> %s )' % (A2, AB)), w.s([u2(leab, '%s <_ %s' % (RA, RB)), u2(leai, '%s <_ %s' % (IA, IB))], 'jca', '( %s -> %s )' % (A2, GEO)), w.s([fcn2, rss2], 'jca', '( %s -> %s )' % (A2, FCN))], '3jca', '( %s -> %s )' % (A2, PS)), w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A2, IABx))
iarr = w.s([iabr], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A2, IABx))
b2 = w.s([w.s([dsum], 'oveq2d', '( %s -> ( ( 2 x. %s ) x. %s ) = ( ( 2 x. %s ) x. ( %s x. %s ) ) )' % (A2, KK, DMI, KK, RX, WW)),
          w.s([mu2, w.s([ex_, dcx], 'eqtrd', '( %s -> ( ( 2 x. %s ) x. ( %s x. %s ) ) = x )' % (A2, KK, Z2, WW))], 'breqtrd', '( %s -> ( ( 2 x. %s ) x. ( %s x. %s ) ) <_ x )' % (A2, KK, RX, WW))], 'eqbrtrd',
         '( %s -> ( ( 2 x. %s ) x. %s ) <_ x )' % (A2, KK, DMI))
dmir = w.s([w.s([RES['re']['yre'], RES['re']['xre']], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A2, YR, XR)), w.s([RES['im']['yre'], RES['im']['xre']], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A2, TI2, SI))], 'readdcld', '( %s -> %s e. RR )' % (A2, DMI))
xre2 = w.s([xrp, w.inst('rpre')], 'syl', '( %s -> x e. RR )' % A2)
lex = w.s([iarr, w.s([m2kr, dmir], 'remulcld', '( %s -> ( ( 2 x. %s ) x. %s ) e. RR )' % (A2, KK, DMI)), xre2, bnd, b2], 'letrd', '( %s -> ( abs ` %s ) <_ x )' % (A2, IABx))
lex0 = w.s([lex, w.s([w.s([w.s([xrp, w.inst('rpcn')], 'syl', '( %s -> x e. CC )' % A2)], 'addlidd', '( %s -> ( 0 + x ) = x )' % A2)], 'eqcomd', '( %s -> x = ( 0 + x ) )' % A2)], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( 0 + x ) )' % (A2, IABx))
ral = w.s([lex0], 'ralrimiva', '( %s -> A. x e. RR+ ( abs ` %s ) <_ ( 0 + x ) )' % (A1, IABx))
iar1 = w.s([w.s([w.s([u1(ac, 'A e. CC'), u1(bc, 'B e. CC')], 'jca', '( %s -> %s )' % (A1, AB)), w.s([u1(leab, '%s <_ %s' % (RA, RB)), u1(leai, '%s <_ %s' % (IA, IB))], 'jca', '( %s -> %s )' % (A1, GEO)), w.s([u1(fcn, 'F e. ( D -cn-> CC )'), u1(rssd, '( A crect B ) C_ D')], 'jca', '( %s -> %s )' % (A1, FCN))], '3jca', '( %s -> %s )' % (A1, PS)), w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A1, IABx))
iarr1 = w.s([iar1], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, IABx))
le01 = w.s([w.s([iarr1, closed(w, A1, '0re', '0 e. RR'), w.inst('alrple')], 'syl2anc', '( %s -> ( ( abs ` %s ) <_ 0 <-> A. x e. RR+ ( abs ` %s ) <_ ( 0 + x ) ) )' % (A1, IABx, IABx)), ral], 'mpbird', '( %s -> ( abs ` %s ) <_ 0 )' % (A1, IABx))
imq = w.s([le01], 'expr', '( ( %s /\\ q e. RR+ ) -> ( %s -> ( abs ` %s ) <_ 0 ) )' % (A0, CNAq, IABx))
rxq = w.s([imq], 'rexlimdva', '( %s -> ( E. q e. RR+ %s -> ( abs ` %s ) <_ 0 ) )' % (A0, CNAq, IABx))
le0 = w.s([cni, rxq], 'mpd', '( %s -> ( abs ` %s ) <_ 0 )' % (A0, IABx))
psf = w.s([w.s([ac, bc], 'jca', '( %s -> %s )' % (A0, AB)), w.s([leab, leai], 'jca', '( %s -> %s )' % (A0, GEO)), w.s([fcn, rssd], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
icl = w.s([psf, w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A0, IABx))
iar0 = w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, IABx))
eq0 = w.s([w.s([iar0, closed(w, A0, '0re', '0 e. RR'), w.inst('letri3')], 'syl2anc', '( %s -> ( ( abs ` %s ) = 0 <-> ( ( abs ` %s ) <_ 0 /\\ 0 <_ ( abs ` %s ) ) ) )' % (A0, IABx, IABx, IABx)),
           w.s([le0, w.s([icl], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, IABx))], 'jca', '( %s -> ( ( abs ` %s ) <_ 0 /\\ 0 <_ ( abs ` %s ) ) )' % (A0, IABx, IABx))], 'mpbird', '( %s -> ( abs ` %s ) = 0 )' % (A0, IABx))
w.qed([eq0, w.s([icl, w.inst('abs00')], 'syl', '( %s -> ( ( abs ` %s ) = 0 <-> %s = 0 ) )' % (A0, IABx, IABx))], 'mpbid', '( %s -> %s = 0 )' % (A0, IABx))
run(w)
