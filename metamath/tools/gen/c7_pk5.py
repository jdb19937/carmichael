"""C7, Perron block 5: the logarithmic affine integral over the unit parameter
(affpos, logaffdv, logaffibl, logaffitg)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, nlinarith, lineq

X = '( 0 (,) 1 )'
XC = '( 0 [,] 1 )'
K = '( Q - P )'
TOP = '( TopOpen ` CCfld )'
JR = '( %s |`t RR )' % TOP
PQ = '( P e. RR+ /\\ Q e. RR+ )'


def WT(t):
    return '( P + ( %s x. %s ) )' % (t, K)


def LQ(t):
    return '( ( Q - P ) / %s )' % WT(t)


# ---------------------------------------------------------------- affpos
A0 = '( %s /\\ T e. %s )' % (PQ, XC)
w = W('affpos', 'A convex combination of two positive reals is positive.')
prp = w.s([], 'simpll', '( %s -> P e. RR+ )' % A0)
qrp = w.s([], 'simplr', '( %s -> Q e. RR+ )' % A0)
tu = w.s([], 'simpr', '( %s -> T e. %s )' % (A0, XC))
tel = w.s([tu, w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), w.inst('elicc2')], 'syl2anc',
                    '( %s -> ( T e. %s <-> ( T e. RR /\\ 0 <_ T /\\ T <_ 1 ) ) )' % (A0, XC))], 'mpbid', '( %s -> ( T e. RR /\\ 0 <_ T /\\ T <_ 1 ) )' % A0)
tr = w.s([tel, w.inst('simp1')], 'syl', '( %s -> T e. RR )' % A0)
t0 = w.s([tel, w.inst('simp2')], 'syl', '( %s -> 0 <_ T )' % A0)
t1 = w.s([tel, w.inst('simp3')], 'syl', '( %s -> T <_ 1 )' % A0)
cl = Closure(w, A0, {'P': ('RR+', prp), 'Q': ('RR+', qrp), 'T': [('RR', tr), ('ge0', t0)]})
pr = cl.mem('P', 'RR'); qr = cl.mem('Q', 'RR')
A1 = '( %s /\\ P <_ Q )' % A0
A2 = '( %s /\\ Q <_ P )' % A0
cl1 = Closure(w, A1, {'P': ('RR+', lift(w, prp, A1)), 'Q': ('RR+', lift(w, qrp, A1)), 'T': [('RR', lift(w, tr, A1)), ('ge0', lift(w, t0, A1))]})
b1 = nlinarith(w, A1, [lift(w, t0, A1), lift(w, t1, A1), cl1.gt0('P'), cl1.gt0('Q'), w.s([], 'simpr', '( %s -> P <_ Q )' % A1)], '0 < %s' % WT('T'), closure=cl1)
cl2 = Closure(w, A2, {'P': ('RR+', lift(w, prp, A2)), 'Q': ('RR+', lift(w, qrp, A2)), 'T': [('RR', lift(w, tr, A2)), ('ge0', lift(w, t0, A2))]})
b2 = nlinarith(w, A2, [lift(w, t0, A2), lift(w, t1, A2), cl2.gt0('P'), cl2.gt0('Q'), w.s([], 'simpr', '( %s -> Q <_ P )' % A2)], '0 < %s' % WT('T'), closure=cl2)
tri = w.s([pr, qr, w.inst('letric')], 'syl2anc', '( %s -> ( P <_ Q \\/ Q <_ P ) )' % A0)
w.qed([b1, b2, tri], 'mpjaodan', '( %s -> 0 < %s )' % (A0, WT('T')))
run7(w)


def ctx(w, A0):
    """the common closures under A0 = PQ (or a conjunction starting with it, base a step to PQ)"""
    d = {}
    d['prp'] = w.s([], 'simpl', '( %s -> P e. RR+ )' % A0)
    d['qrp'] = w.s([], 'simpr', '( %s -> Q e. RR+ )' % A0)
    d['pr'] = w.s([d['prp']], 'rpred', '( %s -> P e. RR )' % A0)
    d['qr'] = w.s([d['qrp']], 'rpred', '( %s -> Q e. RR )' % A0)
    d['pc'] = w.s([d['pr']], 'recnd', '( %s -> P e. CC )' % A0)
    d['qc'] = w.s([d['qr']], 'recnd', '( %s -> Q e. CC )' % A0)
    d['kr'] = w.s([d['qr'], d['pr']], 'resubcld', '( %s -> %s e. RR )' % (A0, K))
    d['kc'] = w.s([d['kr']], 'recnd', '( %s -> %s e. CC )' % (A0, K))
    return d


def wtpos(w, ante, t, tcc, prp, qrp):
    """( ante -> WT(t) e. RR+ ) from tcc: ( ante -> t e. XC )"""
    h = w.s([w.s([prp, qrp], 'jca', '( %s -> %s )' % (ante, PQ)), tcc], 'jca', '( %s -> ( %s /\\ %s e. %s ) )' % (ante, PQ, t, XC))
    pos = w.s([h, w.inst('affpos')], 'syl', '( %s -> 0 < %s )' % (ante, WT(t)))
    wr = w.s([w.s([prp], 'rpred', '( %s -> P e. RR )' % ante),
              w.s([w.s([w.s([w.s([], 'unitssre', '%s C_ RR' % XC)], 'a1i', '( %s -> %s C_ RR )' % (ante, XC)), tcc], 'sseldd', '( %s -> %s e. RR )' % (ante, t)),
                   w.s([w.s([qrp], 'rpred', '( %s -> Q e. RR )' % ante), w.s([prp], 'rpred', '( %s -> P e. RR )' % ante)], 'resubcld', '( %s -> %s e. RR )' % (ante, K))],
                  'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (ante, t, K))], 'readdcld', '( %s -> %s e. RR )' % (ante, WT(t)))
    return w.s([wr, pos], 'elrpd', '( %s -> %s e. RR+ )' % (ante, WT(t)))


# ---------------------------------------------------------------- logaffdv
A0 = PQ
w = W('logaffdv', 'The derivative of ` log ( P + t ( Q - P ) ) ` in the unit parameter is '
      '` ( Q - P ) / ( P + t ( Q - P ) ) `: the primitive of the vertical-edge majorant of '
      'Perron\'s contour in the trivial regime ( ~ dvmptco on ~ dvrelog ).')
d = ctx(w, A0)
pc, qc, kc, kr = d['pc'], d['qc'], d['kc'], d['kr']
jeq = w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)
xopn = w.s([a1(w, A0, 'iooretop', '%s e. ( topGen ` ran (,) )' % X), w.s([jeq], 'a1i', '( %s -> ( topGen ` ran (,) ) = %s )' % (A0, JR))], 'eleqtrd',
           '( %s -> %s e. %s )' % (A0, X, JR))
jform = w.s([], 'eqid', '%s = %s' % (JR, JR))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
sr = a1(w, A0, 'prid1', 'RR e. { RR , CC }')
xss = a1(w, A0, 'ioossre', '%s C_ RR' % X)
dvi = w.s([sr], 'dvmptid', '( %s -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )' % A0)
AT = '( %s /\\ t e. %s )' % (A0, X)
tr = w.s([w.s([xss], 'adantr', '( %s -> %s C_ RR )' % (AT, X)), w.s([], 'simpr', '( %s -> t e. %s )' % (AT, X))], 'sseldd', '( %s -> t e. RR )' % AT)
tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % AT)
one = a1(w, AT, 'ax-1cn', '1 e. CC')
zc = a1(w, AT, '0cn', '0 e. CC')
ARR = '( %s /\\ t e. RR )' % A0
trr = w.s([], 'simpr', '( %s -> t e. RR )' % ARR)
tcr = w.s([trr], 'recnd', '( %s -> t e. CC )' % ARR)
oner = a1(w, ARR, 'ax-1cn', '1 e. CC')
zcr = a1(w, ARR, '0cn', '0 e. CC')
kcr = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ARR, K))
pcr = w.s([pc], 'adantr', '( %s -> P e. CC )' % ARR)
dvi2 = w.s([sr, tcr, oner, dvi, xss, jform, keq, xopn], 'dvmptres', '( %s -> ( RR _D ( t e. %s |-> t ) ) = ( t e. %s |-> 1 ) )' % (A0, X, X))
dvk = w.s([sr, kc], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> 0 ) )' % (A0, K))
kcd = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (AT, K))
dvk2 = w.s([sr, kcr, zcr, dvk, xss, jform, keq, xopn], 'dvmptres', '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> 0 ) )' % (A0, X, K, X))
dvtk = w.s([sr, tc, one, dvi2, kcd, zc, dvk2], 'dvmptmul', '( %s -> ( RR _D ( t e. %s |-> ( t x. %s ) ) ) = ( t e. %s |-> ( ( 1 x. %s ) + ( 0 x. t ) ) ) )' % (A0, X, K, X, K))
b1 = w.s([w.s([kcd], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (AT, K, K)), w.s([tc], 'mul02d', '( %s -> ( 0 x. t ) = 0 )' % AT)], 'oveq12d',
         '( %s -> ( ( 1 x. %s ) + ( 0 x. t ) ) = ( %s + 0 ) )' % (AT, K, K))
b2 = w.s([b1, w.s([kcd], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (AT, K, K))], 'eqtrd', '( %s -> ( ( 1 x. %s ) + ( 0 x. t ) ) = %s )' % (AT, K, K))
dvtk2 = w.s([dvtk, w.s([b2], 'mpteq2dva', '( %s -> ( t e. %s |-> ( ( 1 x. %s ) + ( 0 x. t ) ) ) = ( t e. %s |-> %s ) )' % (A0, X, K, X, K))], 'eqtrd',
            '( %s -> ( RR _D ( t e. %s |-> ( t x. %s ) ) ) = ( t e. %s |-> %s ) )' % (A0, X, K, X, K))
pcd = w.s([pc], 'adantr', '( %s -> P e. CC )' % AT)
dvp = w.s([sr, pc], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> P ) ) = ( t e. RR |-> 0 ) )' % A0)
dvp2 = w.s([sr, pcr, zcr, dvp, xss, jform, keq, xopn], 'dvmptres', '( %s -> ( RR _D ( t e. %s |-> P ) ) = ( t e. %s |-> 0 ) )' % (A0, X, X))
tkc = w.s([tc, kcd], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (AT, K))
dvw = w.s([sr, pcd, zc, dvp2, tkc, kcd, dvtk2], 'dvmptadd', '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> ( 0 + %s ) ) )' % (A0, X, WT('t'), X, K))
dvw2 = w.s([dvw, w.s([w.s([kcd], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AT, K, K))], 'mpteq2dva', '( %s -> ( t e. %s |-> ( 0 + %s ) ) = ( t e. %s |-> %s ) )' % (A0, X, K, X, K))],
           'eqtrd', '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> %s ) )' % (A0, X, WT('t'), X, K))
# the log derivative as a mapping in y
LR = '( log |` RR+ )'
LM = '( y e. RR+ |-> ( log ` y ) )'
RM = '( y e. RR+ |-> ( 1 / y ) )'
lf = w.s([a1(w, A0, 'relogf1o', '%s : RR+ -1-1-onto-> RR' % LR), w.inst('f1of')], 'syl', '( %s -> %s : RR+ --> RR )' % (A0, LR))
lfe = w.s([lf], 'feqmptd', '( %s -> %s = ( y e. RR+ |-> ( %s ` y ) ) )' % (A0, LR, LR))
AY = '( %s /\\ y e. RR+ )' % A0
yrp = w.s([], 'simpr', '( %s -> y e. RR+ )' % AY)
fvr = w.s([yrp, w.inst('fvres')], 'syl', '( %s -> ( %s ` y ) = ( log ` y ) )' % (AY, LR))
lfe2 = w.s([lfe, w.s([fvr], 'mpteq2dva', '( %s -> ( y e. RR+ |-> ( %s ` y ) ) = %s )' % (A0, LR, LM))], 'eqtrd', '( %s -> %s = %s )' % (A0, LR, LM))
dvl = a1(w, A0, 'dvrelog', '( RR _D %s ) = ( x e. RR+ |-> ( 1 / x ) )' % LR)
cbv = w.s([w.s([], 'oveq2', '( x = y -> ( 1 / x ) = ( 1 / y ) )')], 'cbvmptv', '( x e. RR+ |-> ( 1 / x ) ) = %s' % RM)
dvl2 = w.s([w.s([w.s([lfe2], 'eqcomd', '( %s -> %s = %s )' % (A0, LM, LR))], 'oveq2d', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0, LM, LR)),
            w.s([dvl, w.s([cbv], 'a1i', '( %s -> ( x e. RR+ |-> ( 1 / x ) ) = %s )' % (A0, RM))], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, LR, RM))], 'eqtrd',
           '( %s -> ( RR _D %s ) = %s )' % (A0, LM, RM))
# dvmptco
prpt = w.s([d['prp']], 'adantr', '( %s -> P e. RR+ )' % AT); qrpt = w.s([d['qrp']], 'adantr', '( %s -> Q e. RR+ )' % AT)
tcc = w.s([a1(w, AT, 'ioossicc', '%s C_ %s' % (X, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (AT, X))], 'sseldd', '( %s -> t e. %s )' % (AT, XC))
wrp = wtpos(w, AT, 't', tcc, prpt, qrpt)
lyc = w.s([w.s([yrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` y ) e. RR )' % AY)], 'recnd', '( %s -> ( log ` y ) e. CC )' % AY)
ryc = w.s([w.s([yrp], 'rpreccld', '( %s -> ( 1 / y ) e. RR+ )' % AY)], 'rpcnd', '( %s -> ( 1 / y ) e. CC )' % AY)
se = w.s([], 'fveq2', '( y = %s -> ( log ` y ) = ( log ` %s ) )' % (WT('t'), WT('t')))
sf = w.s([], 'oveq2', '( y = %s -> ( 1 / y ) = ( 1 / %s ) )' % (WT('t'), WT('t')))
co = w.s([sr, sr, wrp, kcd, lyc, ryc, dvw2, dvl2, se, sf], 'dvmptco',
         '( %s -> ( RR _D ( t e. %s |-> ( log ` %s ) ) ) = ( t e. %s |-> ( ( 1 / %s ) x. %s ) ) )' % (A0, X, WT('t'), X, WT('t'), K))
bod = w.s([w.s([kcd, w.s([wrp], 'rpcnd', '( %s -> %s e. CC )' % (AT, WT('t'))), w.s([wrp], 'rpne0d', '( %s -> %s =/= 0 )' % (AT, WT('t')))], 'divrec2d',
               '( %s -> %s = ( ( 1 / %s ) x. %s ) )' % (AT, LQ('t'), WT('t'), K))], 'eqcomd', '( %s -> ( ( 1 / %s ) x. %s ) = %s )' % (AT, WT('t'), K, LQ('t')))
w.qed([co, w.s([bod], 'mpteq2dva', '( %s -> ( t e. %s |-> ( ( 1 / %s ) x. %s ) ) = ( t e. %s |-> %s ) )' % (A0, X, WT('t'), K, X, LQ('t')))], 'eqtrd',
      '( %s -> ( RR _D ( t e. %s |-> ( log ` %s ) ) ) = ( t e. %s |-> %s ) )' % (A0, X, WT('t'), X, LQ('t')))
run7(w)

# ---------------------------------------------------------------- logaffibl
HC = '( t e. %s |-> %s )' % (XC, LQ('t'))
HO = '( t e. %s |-> %s )' % (X, LQ('t'))
WC = '( t e. %s |-> %s )' % (XC, WT('t'))
w = W('logaffibl', 'The logarithmic affine integrand is continuous and integrable on the open '
      'unit parameter interval (continuous on the closed one, ~ divcncf , ~ cniccibl ).')
d = ctx(w, A0)
pc, qc, kc, kr = d['pc'], d['qc'], d['kc'], d['kr']
ussr = a1(w, A0, 'unitssre', '%s C_ RR' % XC)
usscn = w.s([ussr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XC))
sscc = a1(w, A0, 'ssid', 'CC C_ CC')
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
kcst = w.s([kc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, K, XC))
pcst = w.s([pc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> P ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
mul1 = w.s([idc, kcst], 'mulcncf', '( %s -> ( t e. %s |-> ( t x. %s ) ) e. ( %s -cn-> CC ) )' % (A0, XC, K, XC))
wcn = w.s([pcst, mul1], 'addcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, WC, XC))
ATC = '( %s /\\ t e. %s )' % (A0, XC)
tcc = w.s([], 'simpr', '( %s -> t e. %s )' % (ATC, XC))
wrp = wtpos(w, ATC, 't', tcc, w.s([d['prp']], 'adantr', '( %s -> P e. RR+ )' % ATC), w.s([d['qrp']], 'adantr', '( %s -> Q e. RR+ )' % ATC))
wd = w.s([w.s([wrp], 'rpcnd', '( %s -> %s e. CC )' % (ATC, WT('t'))), w.s([wrp], 'rpne0d', '( %s -> %s =/= 0 )' % (ATC, WT('t'))), w.inst('eldifsn')], 'sylanbrc',
         '( %s -> %s e. %s )' % (ATC, WT('t'), DOM))
wf = w.s([wd, w.s([], 'eqid', '%s = %s' % (WC, WC))], 'fmptd', '( %s -> %s : %s --> %s )' % (A0, WC, XC, DOM))
dss = a1(w, A0, 'difss', '%s C_ CC' % DOM)
wcn2 = w.s([wf, w.s([dss, wcn, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( %s e. ( %s -cn-> %s ) <-> %s : %s --> %s ) )' % (A0, WC, XC, DOM, WC, XC, DOM))], 'mpbird',
           '( %s -> %s e. ( %s -cn-> %s ) )' % (A0, WC, XC, DOM))
hccn = w.s([kcst, wcn2], 'divcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, HC, XC))
hcc = w.s([w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K)), w.s([wrp], 'rpcnd', '( %s -> %s e. CC )' % (ATC, WT('t'))), w.s([wrp], 'rpne0d', '( %s -> %s =/= 0 )' % (ATC, WT('t')))],
          'divcld', '( %s -> %s e. CC )' % (ATC, LQ('t')))
ioss = a1(w, A0, 'ioossicc', '%s C_ %s' % (X, XC))
rci = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, XC, HC, X, X))
hres = w.s([hccn, w.s([rci], 'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, HC, XC, HC, X, X))], 'mpd',
           '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0, HC, X, X))
rsm = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (HC, X, HO))
hocn = w.s([w.s([w.s([rsm], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A0, HC, X, HO))], 'eqcomd', '( %s -> %s = ( %s |` %s ) )' % (A0, HO, HC, X)), hres], 'eqeltrd',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, HO, X))
hcibl = w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), hccn, w.inst('cniccibl')], 'syl3anc', '( %s -> %s e. L^1 )' % (A0, HC))
hoibl = w.s([ioss, a1(w, A0, 'ioombl', '%s e. dom vol' % X), hcc, hcibl], 'iblss', '( %s -> %s e. L^1 )' % (A0, HO))
w.qed([hocn, hoibl], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (A0, HO, X, HO))
run7(w)

# ---------------------------------------------------------------- logaffitg
GPC = '( t e. %s |-> ( log ` %s ) )' % (XC, WT('t'))
GPO = '( t e. %s |-> ( log ` %s ) )' % (X, WT('t'))
GPCA = '( a e. %s |-> ( log ` %s ) )' % (XC, WT('a'))
w = W('logaffitg', 'The logarithmic affine integral over the unit parameter: '
      '` S. ( 0 (,) 1 ) ( Q - P ) / ( P + t ( Q - P ) ) _d t = log Q - log P ` ( ~ ftc2 , '
      '~ logaffdv ); Lean\'s ` integral_inv_of_pos ` in the parametrisation of ~ lintle .')
d = ctx(w, A0)
pc, qc, kc, kr = d['pc'], d['qc'], d['kc'], d['kr']
r0 = a1(w, A0, '0re', '0 e. RR'); r1 = a1(w, A0, '1re', '1 e. RR'); le01 = a1(w, A0, '0le1', '0 <_ 1')
ussr = a1(w, A0, 'unitssre', '%s C_ RR' % XC)
usscn = w.s([ussr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XC))
sscc = a1(w, A0, 'ssid', 'CC C_ CC')
ATC = '( %s /\\ t e. %s )' % (A0, XC)
tcc = w.s([], 'simpr', '( %s -> t e. %s )' % (ATC, XC))
wrp = wtpos(w, ATC, 't', tcc, w.s([d['prp']], 'adantr', '( %s -> P e. RR+ )' % ATC), w.s([d['qrp']], 'adantr', '( %s -> Q e. RR+ )' % ATC))
# the primitive is continuous on the closed interval: log o. ( t |-> WT )
WC = '( t e. %s |-> %s )' % (XC, WT('t'))
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
kcst = w.s([kc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, K, XC))
pcst = w.s([pc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> P ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
wcn = w.s([pcst, w.s([idc, kcst], 'mulcncf', '( %s -> ( t e. %s |-> ( t x. %s ) ) e. ( %s -cn-> CC ) )' % (A0, XC, K, XC))], 'addcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, WC, XC))
wf = w.s([wrp, w.s([], 'eqid', '%s = %s' % (WC, WC))], 'fmptd', '( %s -> %s : %s --> RR+ )' % (A0, WC, XC))
rpss = a1(w, A0, 'rpssre', 'RR+ C_ RR')
rpsscn = w.s([rpss, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> RR+ C_ CC )' % A0)
wcn2 = w.s([wf, w.s([rpsscn, wcn, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( %s e. ( %s -cn-> RR+ ) <-> %s : %s --> RR+ ) )' % (A0, WC, XC, WC, XC))], 'mpbird',
           '( %s -> %s e. ( %s -cn-> RR+ ) )' % (A0, WC, XC))
LR = '( log |` RR+ )'
LM = '( y e. RR+ |-> ( log ` y ) )'
lcn = a1(w, A0, 'relogcn', '%s e. ( RR+ -cn-> RR )' % LR)
cmp = w.s([wcn2, lcn], 'cncfco', '( %s -> ( %s o. %s ) e. ( %s -cn-> RR ) )' % (A0, LR, WC, XC))
lf = w.s([a1(w, A0, 'relogf1o', '%s : RR+ -1-1-onto-> RR' % LR), w.inst('f1of')], 'syl', '( %s -> %s : RR+ --> RR )' % (A0, LR))
lfe = w.s([lf], 'feqmptd', '( %s -> %s = ( y e. RR+ |-> ( %s ` y ) ) )' % (A0, LR, LR))
AY = '( %s /\\ y e. RR+ )' % A0
yrp = w.s([], 'simpr', '( %s -> y e. RR+ )' % AY)
lfe2 = w.s([lfe, w.s([w.s([yrp, w.inst('fvres')], 'syl', '( %s -> ( %s ` y ) = ( log ` y ) )' % (AY, LR))], 'mpteq2dva', '( %s -> ( y e. RR+ |-> ( %s ` y ) ) = %s )' % (A0, LR, LM))],
           'eqtrd', '( %s -> %s = %s )' % (A0, LR, LM))
coeq = w.s([wrp, w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, WC, WC)), lfe2, w.s([], 'fveq2', '( y = %s -> ( log ` y ) = ( log ` %s ) )' % (WT('t'), WT('t')))], 'fmptco',
           '( %s -> ( %s o. %s ) = %s )' % (A0, LR, WC, GPC))
gcnr = w.s([coeq, cmp], 'eqeltrrd', '( %s -> %s e. ( %s -cn-> RR ) )' % (A0, GPC, XC))
gpccn = w.s([w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), sscc, w.inst('cncfss')], 'syl2anc', '( %s -> ( %s -cn-> RR ) C_ ( %s -cn-> CC ) )' % (A0, XC, XC)), gcnr], 'sseldd',
            '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GPC, XC))
# the derivative on the closed interval equals the one on the open one
jform = w.s([], 'eqid', '%s = %s' % (JR, JR))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
gcl = w.s([w.s([wrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (ATC, WT('t')))], 'recnd', '( %s -> ( log ` %s ) e. CC )' % (ATC, WT('t')))
icc0 = w.s([r0, r1, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s )' % (A0, XC, X))
jeq2 = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)], 'eqcomi', '%s = ( topGen ` ran (,) )' % JR)
icc = w.s([w.s([w.s([jeq2], 'a1i', '( %s -> %s = ( topGen ` ran (,) ) )' % (A0, JR))], 'fveq2d', '( %s -> ( int ` %s ) = ( int ` ( topGen ` ran (,) ) ) )' % (A0, JR))], 'fveq1d',
          '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s ) )' % (A0, JR, XC, XC))
icc2 = w.s([icc, icc0], 'eqtrd', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, JR, XC, X))
ntr = w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), ussr, gcl, jform, keq, icc2], 'dvmptntr', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0, GPC, GPO))
HO = '( t e. %s |-> %s )' % (X, LQ('t'))
dvo = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('logaffdv')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, GPO, HO))
dvf = w.s([ntr, dvo], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, GPC, HO))
cbvs = w.s([w.s([w.s([w.s([], 'oveq1', '( t = a -> ( t x. %s ) = ( a x. %s ) )' % (K, K))], 'oveq2d', '( t = a -> %s = %s )' % (WT('t'), WT('a')))], 'fveq2d',
                '( t = a -> ( log ` %s ) = ( log ` %s ) )' % (WT('t'), WT('a')))], 'cbvmptv', '%s = %s' % (GPC, GPCA))
cbvd = w.s([cbvs], 'a1i', '( %s -> %s = %s )' % (A0, GPC, GPCA))
dvfa = w.s([w.s([w.s([cbvd], 'eqcomd', '( %s -> %s = %s )' % (A0, GPCA, GPC))], 'oveq2d', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0, GPCA, GPC)), dvf], 'eqtrd',
           '( %s -> ( RR _D %s ) = %s )' % (A0, GPCA, HO))
ibl = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('logaffibl')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (A0, HO, X, HO))
hocn = w.s([ibl, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, HO, X))
hoibl = w.s([ibl, w.inst('simpr')], 'syl', '( %s -> %s e. L^1 )' % (A0, HO))
dcn = w.s([w.s([dvfa], 'eqcomd', '( %s -> %s = ( RR _D %s ) )' % (A0, HO, GPCA)), hocn], 'eqeltrrd', '( %s -> ( RR _D %s ) e. ( %s -cn-> CC ) )' % (A0, GPCA, X))
dib = w.s([w.s([dvfa], 'eqcomd', '( %s -> %s = ( RR _D %s ) )' % (A0, HO, GPCA)), hoibl], 'eqeltrrd', '( %s -> ( RR _D %s ) e. L^1 )' % (A0, GPCA))
gpccna = w.s([w.s([cbvd], 'eqcomd', '( %s -> %s = %s )' % (A0, GPCA, GPC)), gpccn], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GPCA, XC))
ftc = w.s([r0, r1, le01, dcn, dib, gpccna], 'ftc2', '( %s -> S. %s ( ( RR _D %s ) ` t ) _d t = ( ( %s ` 1 ) - ( %s ` 0 ) ) )' % (A0, X, GPCA, GPCA, GPCA))
ATO = '( %s /\\ t e. %s )' % (A0, X)
hval = w.s([w.s([w.s([], 'eqid', '%s = %s' % (HO, HO))], 'a1i', '( %s -> %s = %s )' % (A0, HO, HO)), a1(w, ATO, 'ovex', '%s e. _V' % LQ('t'))], 'fvmpt2d', '( %s -> ( %s ` t ) = %s )' % (ATO, HO, LQ('t')))
dval = w.s([w.s([w.s([dvfa], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (ATO, GPCA, HO))], 'fveq1d', '( %s -> ( ( RR _D %s ) ` t ) = ( %s ` t ) )' % (ATO, GPCA, HO)), hval], 'eqtrd',
           '( %s -> ( ( RR _D %s ) ` t ) = %s )' % (ATO, GPCA, LQ('t')))
itg = w.s([dval], 'itgeq2dv', '( %s -> S. %s ( ( RR _D %s ) ` t ) _d t = S. %s %s _d t )' % (A0, X, GPCA, X, LQ('t')))
one1 = a1(w, A0, '1elunit', '1 e. %s' % XC); zero1 = a1(w, A0, '0elunit', '0 e. %s' % XC)
def val(num, sub):
    return w.s([num, a1(w, A0, 'fvex', '( log ` %s ) e. _V' % WT(sub)),
                w.s([w.s([w.s([w.s([], 'oveq1', '( a = %s -> ( a x. %s ) = ( %s x. %s ) )' % (sub, K, sub, K))], 'oveq2d', '( a = %s -> %s = %s )' % (sub, WT('a'), WT(sub)))], 'fveq2d',
                         '( a = %s -> ( log ` %s ) = ( log ` %s ) )' % (sub, WT('a'), WT(sub))), w.s([], 'eqid', '%s = %s' % (GPCA, GPCA))], 'fvmptg',
                    '( ( %s e. %s /\\ ( log ` %s ) e. _V ) -> ( %s ` %s ) = ( log ` %s ) )' % (sub, XC, WT(sub), GPCA, sub, WT(sub)))], 'syl2anc',
               '( %s -> ( %s ` %s ) = ( log ` %s ) )' % (A0, GPCA, sub, WT(sub)))
v1 = val(one1, '1'); v0 = val(zero1, '0')
pk1 = w.s([w.s([w.s([kc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, K, K))], 'oveq2d', '( %s -> %s = ( P + %s ) )' % (A0, WT('1'), K)),
           w.s([pc, qc], 'pncan3d', '( %s -> ( P + %s ) = Q )' % (A0, K))], 'eqtrd', '( %s -> %s = Q )' % (A0, WT('1')))
pk0 = w.s([w.s([w.s([kc], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (A0, K))], 'oveq2d', '( %s -> %s = ( P + 0 ) )' % (A0, WT('0'))),
           w.s([pc], 'addridd', '( %s -> ( P + 0 ) = P )' % A0)], 'eqtrd', '( %s -> %s = P )' % (A0, WT('0')))
v1b = w.s([v1, w.s([pk1], 'fveq2d', '( %s -> ( log ` %s ) = ( log ` Q ) )' % (A0, WT('1')))], 'eqtrd', '( %s -> ( %s ` 1 ) = ( log ` Q ) )' % (A0, GPCA))
v0b = w.s([v0, w.s([pk0], 'fveq2d', '( %s -> ( log ` %s ) = ( log ` P ) )' % (A0, WT('0')))], 'eqtrd', '( %s -> ( %s ` 0 ) = ( log ` P ) )' % (A0, GPCA))
w.qed([w.s([itg], 'eqcomd', '( %s -> S. %s %s _d t = S. %s ( ( RR _D %s ) ` t ) _d t )' % (A0, X, LQ('t'), X, GPCA)),
       w.s([ftc, w.s([v1b, v0b], 'oveq12d', '( %s -> ( ( %s ` 1 ) - ( %s ` 0 ) ) = ( ( log ` Q ) - ( log ` P ) ) )' % (A0, GPCA, GPCA))], 'eqtrd',
           '( %s -> S. %s ( ( RR _D %s ) ` t ) _d t = ( ( log ` Q ) - ( log ` P ) ) )' % (A0, X, GPCA))],
      'eqtrd', '( %s -> S. %s %s _d t = ( ( log ` Q ) - ( log ` P ) ) )' % (A0, X, LQ('t')))
run7(w)
