"""Sortie A3, batch 6: the smoothness bound lambdaL Q <_ Z ^ ( Y + 1 )
(Lean: lambdaL_le_powW / lambdaL_le_pow), through the comparison product
prod_ d e. ( ( 0 ... Y ) i^i Prime ) ( d ^ ( d Nlog Z ) )."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a3lib
from a3lib import fpp, FPP, FP0
from tm import *
from lin import linarith
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

PY = '( ( 0 ... Y ) i^i Prime )'
PYR = '( %s \\ { r } )' % PY
MK = 'prod_ d e. %s ( d ^ ( d Nlog Z ) )' % PY
MKR = 'prod_ d e. %s ( d ^ ( d Nlog Z ) )' % PYR
LA = '( lambdaL ` Q )'
SM = 'A. p e. Prime ( p || ( P - 1 ) -> p <_ Y )'
POW = lambda X: '( %s ^ ( %s Nlog Z ) )' % (X, X)


def pyctx(w, H, znn):
    """PY and MK closures under H (H must not contain the bound variable d)"""
    fz = w.s([], 'fzfid', '( %s -> ( 0 ... Y ) e. Fin )' % H)
    pyss = w.s([w.s([], 'inss1', '%s C_ ( 0 ... Y )' % PY)], 'a1i', '( %s -> %s C_ ( 0 ... Y ) )' % (H, PY))
    pyfin = w.s([fz, pyss, w.inst('ssfi')], 'syl2anc', '( %s -> %s e. Fin )' % (H, PY))
    pyprm = w.s([w.s([], 'inss2', '%s C_ Prime' % PY)], 'a1i', '( %s -> %s C_ Prime )' % (H, PY))
    HD = '( %s /\\ d e. %s )' % (H, PY)
    dp = w.s([w.s([pyprm], 'adantr', '( %s -> %s C_ Prime )' % (HD, PY)), w.s([], 'simpr', '( %s -> d e. %s )' % (HD, PY))], 'sseldd', '( %s -> d e. Prime )' % HD)
    dnn = w.s([dp, w.inst('prmnn')], 'syl', '( %s -> d e. NN )' % HD)
    znnd = w.s([znn], 'adantr', '( %s -> Z e. NN )' % HD)
    dlog = w.s([w.s([dnn], 'nnnn0d', '( %s -> d e. NN0 )' % HD), w.s([znnd], 'nnnn0d', '( %s -> Z e. NN0 )' % HD), w.inst('nlogcl')], 'syl2anc', '( %s -> ( d Nlog Z ) e. NN0 )' % HD)
    dpow = w.s([dnn, dlog], 'nnexpcld', '( %s -> %s e. NN )' % (HD, POW('d')))
    mknn = w.s([pyfin, dpow], 'fprodnncl', '( %s -> %s e. NN )' % (H, MK))
    mkz = w.s([mknn], 'nnzd', '( %s -> %s e. ZZ )' % (H, MK))
    mkn0 = w.s([mknn], 'nnne0d', '( %s -> %s =/= 0 )' % (H, MK))
    return dict(pyfin=pyfin, pyprm=pyprm, pyss=pyss, dnn=dnn, dpow=dpow, mknn=mknn, mkz=mkz, mkn0=mkn0, HD=HD)


def lift(w, step, formula_tail, antes):
    """adantr a step through a chain of antecedents; antes is the list of the
    successive antecedent texts, outermost first (excluding the step's own)"""
    cur = step
    for a in antes:
        cur = w.s([cur], 'adantr', '( %s -> %s )' % (a, formula_tail))
    return cur


# ------------------------------------------------------------ extrwsmdv
w = W('extrwsmdv', 'A y-smooth P - 1 with P <_ z divides the comparison product prod_ d e. ( ( 0 ... y ) i^i Prime ) ( d ^ ( d Nlog z ) ) (the divisibility half of lambdaL_le_powW).')
H = '( ( Z e. NN /\\ Y e. NN0 ) /\\ ( P e. Prime /\\ P <_ Z /\\ %s ) )' % SM
HR = '( %s /\\ r e. Prime )' % H
HA = '( %s /\\ r <_ Y )' % HR
HB = '( %s /\\ -. r <_ Y )' % HR
znn = w.s([], 'simpll', '( %s -> Z e. NN )' % H)
yn0 = w.s([], 'simplr', '( %s -> Y e. NN0 )' % H)
pp = w.s([], 'simpr1', '( %s -> P e. Prime )' % H)
ple = w.s([], 'simpr2', '( %s -> P <_ Z )' % H)
sm = w.s([], 'simpr3', '( %s -> %s )' % (H, SM))
ctx = pyctx(w, H, znn)
puz = w.s([pp, w.inst('prmuz2')], 'syl', '( %s -> P e. ( ZZ>= ` 2 ) )' % H)
p1nn = w.s([puz, w.inst('uz2m1nn')], 'syl', '( %s -> ( P - 1 ) e. NN )' % H)
p1z = w.s([p1nn], 'nnzd', '( %s -> ( P - 1 ) e. ZZ )' % H)
p1n0 = w.s([p1nn], 'nnne0d', '( %s -> ( P - 1 ) =/= 0 )' % H)
pre = w.s([w.s([pp, w.inst('prmnn')], 'syl', '( %s -> P e. NN )' % H)], 'nnred', '( %s -> P e. RR )' % H)
zre = w.s([znn], 'nnred', '( %s -> Z e. RR )' % H)
p1le = linarith(w, H, [ple], '( P - 1 ) <_ Z', leaves={'P': ('RR', pre), 'Z': ('RR', zre)})

# ---- case 1: r <_ Y
rpa = lift(w, w.s([], 'simpr', '( %s -> r e. Prime )' % HR), 'r e. Prime', [HA])
rnnA = w.s([rpa, w.inst('prmnn')], 'syl', '( %s -> r e. NN )' % HA)
rn0A = w.s([rnnA], 'nnnn0d', '( %s -> r e. NN0 )' % HA)
rzA = w.s([rnnA], 'nnzd', '( %s -> r e. ZZ )' % HA)
ruzA = w.s([rpa, w.inst('prmuz2')], 'syl', '( %s -> r e. ( ZZ>= ` 2 ) )' % HA)
znnA = lift(w, znn, 'Z e. NN', [HR, HA])
yn0A = lift(w, yn0, 'Y e. NN0', [HR, HA])
rfz = w.s([w.s([rn0A, yn0A, w.s([], 'simpr', '( %s -> r <_ Y )' % HA)], '3jca', '( %s -> ( r e. NN0 /\\ Y e. NN0 /\\ r <_ Y ) )' % HA), w.inst('elfz2nn0')], 'sylibr', '( %s -> r e. ( 0 ... Y ) )' % HA)
rpy = w.s([w.s([rfz, rpa], 'jca', '( %s -> ( r e. ( 0 ... Y ) /\\ r e. Prime ) )' % HA), w.inst('elin')], 'sylibr', '( %s -> r e. %s )' % (HA, PY))
SB = '( %s /\\ d = r )' % HA
cg, newf = w.congr(POW('d'), {'d': 'r'}, SB, {'d': w.s([], 'simpr', '( %s -> d = r )' % SB)})
assert newf == POW('r'), newf
pyfinA = lift(w, ctx['pyfin'], '%s e. Fin' % PY, [HR, HA])
pyprmA = lift(w, ctx['pyprm'], '%s C_ Prime' % PY, [HR, HA])
HAD = '( %s /\\ d e. %s )' % (HA, PY)
dpowA = w.s([w.s([w.s([ctx['dpow']], 'adantlr', '( ( %s /\\ d e. %s ) -> %s e. NN )' % (HR, PY, POW('d'))), ], 'adantlr', '( %s -> %s e. NN )' % (HAD, POW('d')))], 'nncnd', '( %s -> %s e. CC )' % (HAD, POW('d')))
sp = w.s([pyfinA, dpowA, rpy, cg], 'fprodsplit1', '( %s -> %s = ( %s x. %s ) )' % (HA, MK, POW('r'), MKR))
rlog = w.s([rn0A, w.s([znnA], 'nnnn0d', '( %s -> Z e. NN0 )' % HA), w.inst('nlogcl')], 'syl2anc', '( %s -> ( r Nlog Z ) e. NN0 )' % HA)
rpowz = w.s([rzA, rlog], 'zexpcld', '( %s -> %s e. ZZ )' % (HA, POW('r')))
HADD = '( %s /\\ d e. %s )' % (HA, PYR)
dfin2 = w.s([pyfinA, w.inst('diffi')], 'syl', '( %s -> %s e. Fin )' % (HA, PYR))
dss2 = w.s([pyprmA, w.inst('ssdifss')], 'syl', '( %s -> %s C_ Prime )' % (HA, PYR))
dnn2 = w.s([w.s([w.s([dss2], 'adantr', '( %s -> %s C_ Prime )' % (HADD, PYR)), w.s([], 'simpr', '( %s -> d e. %s )' % (HADD, PYR))], 'sseldd', '( %s -> d e. Prime )' % HADD), w.inst('prmnn')], 'syl', '( %s -> d e. NN )' % HADD)
dlog2 = w.s([w.s([dnn2], 'nnnn0d', '( %s -> d e. NN0 )' % HADD), w.s([w.s([znnA], 'adantr', '( %s -> Z e. NN )' % HADD)], 'nnnn0d', '( %s -> Z e. NN0 )' % HADD), w.inst('nlogcl')], 'syl2anc', '( %s -> ( d Nlog Z ) e. NN0 )' % HADD)
dpow2 = w.s([dnn2, dlog2], 'nnexpcld', '( %s -> %s e. NN )' % (HADD, POW('d')))
restz = w.s([w.s([dfin2, dpow2], 'fprodnncl', '( %s -> %s e. NN )' % (HA, MKR))], 'nnzd', '( %s -> %s e. ZZ )' % (HA, MKR))
dvm = w.s([rpowz, restz, w.inst('dvdsmul1')], 'syl2anc', '( %s -> %s || ( %s x. %s ) )' % (HA, POW('r'), POW('r'), MKR))
dvmk = w.s([dvm, sp], 'breqtrrd', '( %s -> %s || %s )' % (HA, POW('r'), MK))
mkzA = lift(w, ctx['mkz'], '%s e. ZZ' % MK, [HR, HA])
mkn0A = lift(w, ctx['mkn0'], '%s =/= 0' % MK, [HR, HA])
pcb = w.s([w.s([rpa, mkzA, rlog], '3jca', '( %s -> ( r e. Prime /\\ %s e. ZZ /\\ ( r Nlog Z ) e. NN0 ) )' % (HA, MK)), w.inst('pcdvdsb')], 'syl', '( %s -> ( ( r Nlog Z ) <_ ( r pCnt %s ) <-> %s || %s ) )' % (HA, MK, POW('r'), MK))
lemk = w.s([pcb, dvmk], 'mpbird', '( %s -> ( r Nlog Z ) <_ ( r pCnt %s ) )' % (HA, MK))
p1nnA = lift(w, p1nn, '( P - 1 ) e. NN', [HR, HA])
p1zA = lift(w, p1z, '( P - 1 ) e. ZZ', [HR, HA])
p1n0A = lift(w, p1n0, '( P - 1 ) =/= 0', [HR, HA])
pcarg = w.s([rpa, w.s([p1zA, p1n0A], 'jca', '( %s -> ( ( P - 1 ) e. ZZ /\\ ( P - 1 ) =/= 0 ) )' % HA)], 'jca', '( %s -> ( r e. Prime /\\ ( ( P - 1 ) e. ZZ /\\ ( P - 1 ) =/= 0 ) ) )' % HA)
pcn0 = w.s([pcarg, w.inst('pczcl')], 'syl', '( %s -> ( r pCnt ( P - 1 ) ) e. NN0 )' % HA)
pcdv = w.s([pcarg, w.inst('pczdvds')], 'syl', '( %s -> ( r ^ ( r pCnt ( P - 1 ) ) ) || ( P - 1 ) )' % HA)
pcle = w.s([w.s([w.s([rzA, pcn0], 'zexpcld', '( %s -> ( r ^ ( r pCnt ( P - 1 ) ) ) e. ZZ )' % HA), p1nnA, w.inst('dvdsle')], 'syl2anc', '( %s -> ( ( r ^ ( r pCnt ( P - 1 ) ) ) || ( P - 1 ) -> ( r ^ ( r pCnt ( P - 1 ) ) ) <_ ( P - 1 ) ) )' % HA), pcdv], 'mpd', '( %s -> ( r ^ ( r pCnt ( P - 1 ) ) ) <_ ( P - 1 ) )' % HA)
p1leA = lift(w, p1le, '( P - 1 ) <_ Z', [HR, HA])
powre = w.s([w.s([rnnA, pcn0], 'nnexpcld', '( %s -> ( r ^ ( r pCnt ( P - 1 ) ) ) e. NN )' % HA)], 'nnred', '( %s -> ( r ^ ( r pCnt ( P - 1 ) ) ) e. RR )' % HA)
p1reA = w.s([p1nnA], 'nnred', '( %s -> ( P - 1 ) e. RR )' % HA)
zreA = w.s([znnA], 'nnred', '( %s -> Z e. RR )' % HA)
powleZ = w.s([powre, p1reA, zreA, pcle, p1leA], 'letrd', '( %s -> ( r ^ ( r pCnt ( P - 1 ) ) ) <_ Z )' % HA)
ub = w.s([w.s([w.s([ruzA, znnA], 'jca', '( %s -> ( r e. ( ZZ>= ` 2 ) /\\ Z e. NN ) )' % HA), w.s([pcn0, powleZ], 'jca', '( %s -> ( ( r pCnt ( P - 1 ) ) e. NN0 /\\ ( r ^ ( r pCnt ( P - 1 ) ) ) <_ Z ) )' % HA)], 'jca', '( %s -> ( ( r e. ( ZZ>= ` 2 ) /\\ Z e. NN ) /\\ ( ( r pCnt ( P - 1 ) ) e. NN0 /\\ ( r ^ ( r pCnt ( P - 1 ) ) ) <_ Z ) ) )' % HA), w.inst('nlogub')], 'syl', '( %s -> ( r pCnt ( P - 1 ) ) <_ ( r Nlog Z ) )' % HA)
pcmkA = w.s([w.s([w.s([rpa, w.s([mkzA, mkn0A], 'jca', '( %s -> ( %s e. ZZ /\\ %s =/= 0 ) )' % (HA, MK, MK))], 'jca', '( %s -> ( r e. Prime /\\ ( %s e. ZZ /\\ %s =/= 0 ) ) )' % (HA, MK, MK)), w.inst('pczcl')], 'syl', '( %s -> ( r pCnt %s ) e. NN0 )' % (HA, MK))], 'nn0red', '( %s -> ( r pCnt %s ) e. RR )' % (HA, MK))
caseA = w.s([w.s([pcn0], 'nn0red', '( %s -> ( r pCnt ( P - 1 ) ) e. RR )' % HA), w.s([rlog], 'nn0red', '( %s -> ( r Nlog Z ) e. RR )' % HA), pcmkA, ub, lemk], 'letrd', '( %s -> ( r pCnt ( P - 1 ) ) <_ ( r pCnt %s ) )' % (HA, MK))

# ---- case 2: Y < r, so r does not divide P - 1
rpb = lift(w, w.s([], 'simpr', '( %s -> r e. Prime )' % HR), 'r e. Prime', [HB])
smB = lift(w, sm, SM, [HR, HB])
cgr, nf2 = w.wcongr('( p || ( P - 1 ) -> p <_ Y )', {'p': 'r'}, 'p = r', {'p': w.s([], 'id', '( p = r -> p = r )')})
assert nf2 == '( r || ( P - 1 ) -> r <_ Y )', nf2
rsp = w.s([cgr], 'rspcv', '( r e. Prime -> ( %s -> ( r || ( P - 1 ) -> r <_ Y ) ) )' % SM)
imB = w.s([w.s([rpb, rsp], 'syl', '( %s -> ( %s -> ( r || ( P - 1 ) -> r <_ Y ) ) )' % (HB, SM)), smB], 'mpd', '( %s -> ( r || ( P - 1 ) -> r <_ Y ) )' % HB)
ndB = w.s([w.s([], 'simpr', '( %s -> -. r <_ Y )' % HB), imB], 'mtod', '( %s -> -. r || ( P - 1 ) )' % HB)
p1nnB = lift(w, p1nn, '( P - 1 ) e. NN', [HR, HB])
pc0 = w.s([w.s([rpb, p1nnB, w.inst('pceq0')], 'syl2anc', '( %s -> ( ( r pCnt ( P - 1 ) ) = 0 <-> -. r || ( P - 1 ) ) )' % HB), ndB], 'mpbird', '( %s -> ( r pCnt ( P - 1 ) ) = 0 )' % HB)
mkzB = lift(w, ctx['mkz'], '%s e. ZZ' % MK, [HR, HB])
ge0 = w.s([rpb, mkzB, w.inst('pcge0')], 'syl2anc', '( %s -> 0 <_ ( r pCnt %s ) )' % (HB, MK))
caseB = w.s([pc0, ge0], 'eqbrtrd', '( %s -> ( r pCnt ( P - 1 ) ) <_ ( r pCnt %s ) )' % (HB, MK))

# ---- assemble
both = w.s([caseA, caseB], 'pm2.61dan', '( %s -> ( r pCnt ( P - 1 ) ) <_ ( r pCnt %s ) )' % (HR, MK))
ral = w.s([both], 'ralrimiva', '( %s -> A. r e. Prime ( r pCnt ( P - 1 ) ) <_ ( r pCnt %s ) )' % (H, MK))
pc2 = w.s([p1z, ctx['mkz'], w.inst('pc2dvds')], 'syl2anc', '( %s -> ( ( P - 1 ) || %s <-> A. r e. Prime ( r pCnt ( P - 1 ) ) <_ ( r pCnt %s ) ) )' % (H, MK, MK))
w.qed([pc2, ral], 'mpbird', '( %s -> ( P - 1 ) || %s )' % (H, MK))
run(w)

# ------------------------------------------------------------ extrwmkle
w = W('extrwmkle', 'The comparison product is at most Z ^ ( Y + 1 ) (the counting half of lambdaL_le_powW).')
H = '( Z e. NN /\\ Y e. NN0 )'
znn = w.s([], 'simpl', '( %s -> Z e. NN )' % H)
yn0 = w.s([], 'simpr', '( %s -> Y e. NN0 )' % H)
ctx = pyctx(w, H, znn)
HD = ctx['HD']
zreD = w.s([w.s([znn], 'adantr', '( %s -> Z e. NN )' % HD)], 'nnred', '( %s -> Z e. RR )' % HD)
dpre = w.s([ctx['dpow']], 'nnred', '( %s -> %s e. RR )' % (HD, POW('d')))
dpge = w.s([ctx['dpow']], 'nngt0d', '( %s -> 0 < %s )' % (HD, POW('d')))
dpge0 = linarith(w, HD, [dpge], '0 <_ %s' % POW('d'), leaves={POW('d'): ('RR', dpre)})
duz = w.s([w.s([w.s([ctx['pyprm']], 'adantr', '( %s -> %s C_ Prime )' % (HD, PY)), w.s([], 'simpr', '( %s -> d e. %s )' % (HD, PY))], 'sseldd', '( %s -> d e. Prime )' % HD), w.inst('prmuz2')], 'syl', '( %s -> d e. ( ZZ>= ` 2 ) )' % HD)
dple = w.s([duz, w.s([znn], 'adantr', '( %s -> Z e. NN )' % HD), w.inst('nlogle')], 'syl2anc', '( %s -> %s <_ Z )' % (HD, POW('d')))
ple = w.s([w.s([], 'nfv', 'F/ d %s' % H), ctx['pyfin'], dpre, dpge0, zreD, dple], 'fprodle', '( %s -> %s <_ prod_ d e. %s Z )' % (H, MK, PY))
pc = w.s([ctx['pyfin'], w.s([znn], 'nncnd', '( %s -> Z e. CC )' % H), w.inst('fprodconst')], 'syl2anc', '( %s -> prod_ d e. %s Z = ( Z ^ ( # ` %s ) ) )' % (H, PY, PY))
le1 = w.s([ple, pc], 'breqtrd', '( %s -> %s <_ ( Z ^ ( # ` %s ) ) )' % (H, MK, PY))
hle = w.s([w.s([], 'fzfid', '( %s -> ( 0 ... Y ) e. Fin )' % H), ctx['pyss'], w.inst('hashssle')], 'syl2anc', '( %s -> ( # ` %s ) <_ ( # ` ( 0 ... Y ) ) )' % (H, PY))
hfz = w.s([yn0, w.inst('hashfz0')], 'syl', '( %s -> ( # ` ( 0 ... Y ) ) = ( Y + 1 ) )' % H)
hle2 = w.s([hle, hfz], 'breqtrd', '( %s -> ( # ` %s ) <_ ( Y + 1 ) )' % (H, PY))
hpyz = w.s([w.s([ctx['pyfin'], w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (H, PY))], 'nn0zd', '( %s -> ( # ` %s ) e. ZZ )' % (H, PY))
y1z = w.s([w.s([yn0], 'nn0zd', '( %s -> Y e. ZZ )' % H), w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % H)], 'zaddcld', '( %s -> ( Y + 1 ) e. ZZ )' % H)
uzst = w.s([w.s([hpyz, y1z, hle2], '3jca', '( %s -> ( ( # ` %s ) e. ZZ /\\ ( Y + 1 ) e. ZZ /\\ ( # ` %s ) <_ ( Y + 1 ) ) )' % (H, PY, PY)), w.inst('eluz2')], 'sylibr', '( %s -> ( Y + 1 ) e. ( ZZ>= ` ( # ` %s ) ) )' % (H, PY))
zre = w.s([znn], 'nnred', '( %s -> Z e. RR )' % H)
zge1 = w.s([znn], 'nnge1d', '( %s -> 1 <_ Z )' % H)
pw = w.s([zre, zge1, uzst, w.inst('leexp2a')], 'syl3anc', '( %s -> ( Z ^ ( # ` %s ) ) <_ ( Z ^ ( Y + 1 ) ) )' % (H, PY))
zrp = w.s([znn], 'nnrpd', '( %s -> Z e. RR+ )' % H)
p1re = w.s([w.s([zrp, hpyz, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( Z ^ ( # ` %s ) ) e. RR+ )' % (H, PY))], 'rpred', '( %s -> ( Z ^ ( # ` %s ) ) e. RR )' % (H, PY))
p2re = w.s([w.s([zrp, y1z, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( Z ^ ( Y + 1 ) ) e. RR+ )' % H)], 'rpred', '( %s -> ( Z ^ ( Y + 1 ) ) e. RR )' % H)
w.qed([w.s([ctx['mknn']], 'nnred', '( %s -> %s e. RR )' % (H, MK)), p1re, p2re, le1, pw], 'letrd', '( %s -> %s <_ ( Z ^ ( Y + 1 ) ) )' % (H, MK))
run(w)

# ------------------------------------------------------------ extrwlamle
w = W('extrwlamle', 'The smoothness bound lambdaL Q <_ Z ^ ( Y + 1 ) for a finite set Q of primes at most Z whose predecessors are Y-smooth (Lean: lambdaL_le_powW, lambdaL_le_pow).')
SMC = 'A. c e. Q ( c <_ Z /\\ A. p e. Prime ( p || ( c - 1 ) -> p <_ Y ) )'
H = '( ( Z e. NN /\\ Y e. NN0 ) /\\ ( Q e. %s /\\ %s ) )' % (FPP, SMC)
MPT = '( q e. Q |-> ( q - 1 ) )'
RAN = 'ran %s' % MPT
SMQ = '( q <_ Z /\\ A. p e. Prime ( p || ( q - 1 ) -> p <_ Y ) )'
znn = w.s([], 'simpll', '( %s -> Z e. NN )' % H)
yn0 = w.s([], 'simplr', '( %s -> Y e. NN0 )' % H)
q1 = w.s([], 'simprl', '( %s -> Q e. %s )' % (H, FPP))
smc = w.s([], 'simprr', '( %s -> %s )' % (H, SMC))
ss, fin, f0 = fpp(w, H, q1)
lamv = w.s([f0, w.inst('lambdalval')], 'syl', '( %s -> %s = ( _lcm ` %s ) )' % (H, LA, RAN))
HQ = '( %s /\\ q e. Q )' % H
qel = w.s([], 'simpr', '( %s -> q e. Q )' % HQ)
qp = w.s([w.s([ss], 'adantr', '( %s -> Q C_ Prime )' % HQ), qel], 'sseldd', '( %s -> q e. Prime )' % HQ)
q1nn = w.s([w.s([qp, w.inst('prmuz2')], 'syl', '( %s -> q e. ( ZZ>= ` 2 ) )' % HQ), w.inst('uz2m1nn')], 'syl', '( %s -> ( q - 1 ) e. NN )' % HQ)
ralnn = w.s([q1nn], 'ralrimiva', '( %s -> A. q e. Q ( q - 1 ) e. NN )' % H)
ralz = w.s([w.s([q1nn], 'nnzd', '( %s -> ( q - 1 ) e. ZZ )' % HQ)], 'ralrimiva', '( %s -> A. q e. Q ( q - 1 ) e. ZZ )' % H)
mpteq = w.s([], 'eqid', '%s = %s' % (MPT, MPT))
rmz = w.s([mpteq], 'rnmptss', '( A. q e. Q ( q - 1 ) e. ZZ -> %s C_ ZZ )' % RAN)
ranz = w.s([ralz, rmz], 'syl', '( %s -> %s C_ ZZ )' % (H, RAN))
rmn = w.s([mpteq], 'rnmptss', '( A. q e. Q ( q - 1 ) e. NN -> %s C_ NN )' % RAN)
rannn = w.s([ralnn, rmn], 'syl', '( %s -> %s C_ NN )' % (H, RAN))
ranfin = w.s([w.s([fin, w.inst('mptfi')], 'syl', '( %s -> %s e. Fin )' % (H, MPT)), w.inst('rnfi')], 'syl', '( %s -> %s e. Fin )' % (H, RAN))
n0nn = w.s([w.s([], '0nnn', '-. 0 e. NN')], 'a1i', '( %s -> -. 0 e. NN )' % H)
n0ran = w.s([w.s([rannn], 'ssneld', '( %s -> ( -. 0 e. NN -> -. 0 e. %s ) )' % (H, RAN)), n0nn], 'mpd', '( %s -> -. 0 e. %s )' % (H, RAN))
nelbi = w.s([w.s([], 'df-nel', '( 0 e/ %s <-> -. 0 e. %s )' % (RAN, RAN))], 'a1i', '( %s -> ( 0 e/ %s <-> -. 0 e. %s ) )' % (H, RAN, RAN))
nel = w.s([nelbi, n0ran], 'mpbird', '( %s -> 0 e/ %s )' % (H, RAN))
cgq, nfq = w.wcongr('( c <_ Z /\\ A. p e. Prime ( p || ( c - 1 ) -> p <_ Y ) )', {'c': 'q'}, 'c = q', {'c': w.s([], 'id', '( c = q -> c = q )')})
assert nfq == SMQ, nfq
rsp = w.s([cgq], 'rspcv', '( q e. Q -> ( %s -> %s ) )' % (SMC, SMQ))
smq = w.s([w.s([qel, rsp], 'syl', '( %s -> ( %s -> %s ) )' % (HQ, SMC, SMQ)), w.s([smc], 'adantr', '( %s -> %s )' % (HQ, SMC))], 'mpd', '( %s -> %s )' % (HQ, SMQ))
qle = w.s([smq], 'simpld', '( %s -> q <_ Z )' % HQ)
qsm = w.s([smq], 'simprd', '( %s -> A. p e. Prime ( p || ( q - 1 ) -> p <_ Y ) )' % HQ)
zyq = w.s([w.s([znn], 'adantr', '( %s -> Z e. NN )' % HQ), w.s([yn0], 'adantr', '( %s -> Y e. NN0 )' % HQ)], 'jca', '( %s -> ( Z e. NN /\\ Y e. NN0 ) )' % HQ)
trip = w.s([qp, qle, qsm], '3jca', '( %s -> ( q e. Prime /\\ q <_ Z /\\ A. p e. Prime ( p || ( q - 1 ) -> p <_ Y ) ) )' % HQ)
sd = w.s([w.s([zyq, trip], 'jca', '( %s -> ( ( Z e. NN /\\ Y e. NN0 ) /\\ ( q e. Prime /\\ q <_ Z /\\ A. p e. Prime ( p || ( q - 1 ) -> p <_ Y ) ) ) )' % HQ), w.inst('extrwsmdv')], 'syl', '( %s -> ( q - 1 ) || %s )' % (HQ, MK))
ralq = w.s([sd], 'ralrimiva', '( %s -> A. q e. Q ( q - 1 ) || %s )' % (H, MK))
cgm = w.s([w.s([], 'id', '( m = ( q - 1 ) -> m = ( q - 1 ) )')], 'breq1d', '( m = ( q - 1 ) -> ( m || %s <-> ( q - 1 ) || %s ) )' % (MK, MK))
rrn = w.s([mpteq, cgm], 'ralrnmpt', '( A. q e. Q ( q - 1 ) e. NN -> ( A. m e. %s m || %s <-> A. q e. Q ( q - 1 ) || %s ) )' % (RAN, MK, MK))
bim = w.s([ralnn, rrn], 'syl', '( %s -> ( A. m e. %s m || %s <-> A. q e. Q ( q - 1 ) || %s ) )' % (H, RAN, MK, MK))
ralm = w.s([bim, ralq], 'mpbird', '( %s -> A. m e. %s m || %s )' % (H, RAN, MK))
ctx = pyctx(w, H, znn)
lcmim = w.s([w.s([ranz, ranfin, nel], '3jca', '( %s -> ( %s C_ ZZ /\\ %s e. Fin /\\ 0 e/ %s ) )' % (H, RAN, RAN, RAN)), w.inst('lcmfledvds')], 'syl', '( %s -> ( ( %s e. NN /\\ A. m e. %s m || %s ) -> ( _lcm ` %s ) <_ %s ) )' % (H, MK, RAN, MK, RAN, MK))
lcmle = w.s([lcmim, w.s([ctx['mknn'], ralm], 'jca', '( %s -> ( %s e. NN /\\ A. m e. %s m || %s ) )' % (H, MK, RAN, MK))], 'mpd', '( %s -> ( _lcm ` %s ) <_ %s )' % (H, RAN, MK))
lale = w.s([lamv, lcmle], 'eqbrtrd', '( %s -> %s <_ %s )' % (H, LA, MK))
mkle = w.s([w.s([znn, yn0], 'jca', '( %s -> ( Z e. NN /\\ Y e. NN0 ) )' % H), w.inst('extrwmkle')], 'syl', '( %s -> %s <_ ( Z ^ ( Y + 1 ) ) )' % (H, MK))
lare = w.s([w.s([q1, w.inst('lambdalcl')], 'syl', '( %s -> %s e. NN )' % (H, LA))], 'nnred', '( %s -> %s e. RR )' % (H, LA))
mkre = w.s([ctx['mknn']], 'nnred', '( %s -> %s e. RR )' % (H, MK))
y1z = w.s([w.s([yn0], 'nn0zd', '( %s -> Y e. ZZ )' % H), w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % H)], 'zaddcld', '( %s -> ( Y + 1 ) e. ZZ )' % H)
zpre = w.s([w.s([w.s([znn], 'nnrpd', '( %s -> Z e. RR+ )' % H), y1z, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( Z ^ ( Y + 1 ) ) e. RR+ )' % H)], 'rpred', '( %s -> ( Z ^ ( Y + 1 ) ) e. RR )' % H)
w.qed([lare, mkre, zpre, lale, mkle], 'letrd', '( %s -> %s <_ ( Z ^ ( Y + 1 ) ) )' % (H, LA))
run(w)
