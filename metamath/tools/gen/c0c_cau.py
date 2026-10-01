"""Sortie C0c batch 10: Cauchy's integral formula for a rectangle."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

CCP = '( CC \\ { P } )'
RINVF = '( z e. %s |-> ( 1 / ( z - P ) ) )' % CCP
RP = RE('P'); IP = IM('P')
INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
PUNC = '( ( A crect B ) \\ { P } )'
EP = '( D \\ { P } )'
QUO = lambda X: '( ( ( F ` %s ) - ( F ` P ) ) / ( %s - P ) )' % (X, X)
CDF = '( ( CC _D F ) ` P )'
DSFC = '( z e. D |-> if ( z = P , %s , %s ) )' % (CDF, QUO('z'))
QPF = '( z e. %s |-> %s )' % (EP, QUO('z'))
G0 = '( z e. %s |-> ( 1 / ( z - P ) ) )' % EP
TGT = '( z e. %s |-> ( ( F ` z ) / ( z - P ) ) )' % PUNC
HOLO = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) )'

# ---- rinvcnss: the reciprocal factor on a subset of the punctured plane
w = W('rinvcnss', 'The function 1 / ( z - P ) is continuous on any set of complex numbers omitting P.')
A0 = '( P e. CC /\\ E C_ %s )' % CCP
pc = w.s([], 'simpl', '( %s -> P e. CC )' % A0)
ess = w.s([], 'simpr', '( %s -> E C_ %s )' % (A0, CCP))
riv = w.s([pc, w.inst('rinvcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RINVF, CCP))
rr = w.s([w.s([ess, w.inst('rescncf')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` E ) e. ( E -cn-> CC ) ) )' % (A0, RINVF, CCP, RINVF)), riv],
         'mpd', '( %s -> ( %s |` E ) e. ( E -cn-> CC ) )' % (A0, RINVF))
rs = w.s([ess, w.inst('resmpt')], 'syl', '( %s -> ( %s |` E ) = ( z e. E |-> ( 1 / ( z - P ) ) ) )' % (A0, RINVF))
w.qed([rs, rr], 'eqeltrrd', '( %s -> ( z e. E |-> ( 1 / ( z - P ) ) ) e. ( E -cn-> CC ) )' % A0); run(w)

# ---- rectintcau: Cauchy's integral formula for a rectangle
w = W('rectintcau', 'Cauchy integral formula for a rectangle: the boundary integral of ( F ` z ) / ( z - P ) with P strictly inside is 2 x. ( _i x. _pi ) times the value at P.')
A0 = '( %s /\\ %s /\\ %s )' % (AB, INT, HOLO)
A1 = '( %s /\\ u e. %s )' % (A0, PUNC)
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
it = w.s([], 'simp2', '( %s -> %s )' % (A0, INT))
ho = w.s([], 'simp3', '( %s -> %s )' % (A0, HOLO))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
fcn = w.s([ho, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rdm = w.s([ho, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lr = w.s([ineq, w.inst('simpll')], 'syl', '( %s -> %s < %s )' % (A0, RA, RP))
rr = w.s([ineq, w.inst('simplr')], 'syl', '( %s -> %s < %s )' % (A0, RP, RB))
li = w.s([ineq, w.inst('simprl')], 'syl', '( %s -> %s < %s )' % (A0, IA, IP))
ri = w.s([ineq, w.inst('simprr')], 'syl', '( %s -> %s < %s )' % (A0, IP, IB))
arr = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
brr = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
air = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bir = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
prr = w.s([pc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RP))
pir = w.s([pc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IP))
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ccs = closed(w, A0, 'ssid', 'CC C_ CC')
dvb = w.s([ccs, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
rd = w.s([rdm, dvb], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
# P is in the closed rectangle
rpi = w.s([w.s([prr, w.s([lr], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RP)), w.s([rr], 'ltled', '( %s -> %s <_ %s )' % (A0, RP, RB))], '3jca',
                '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (A0, RP, RA, RP, RP, RB)),
           w.s([arr, brr, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, RP, RA, RB, RP, RA, RP, RP, RB))],
          'mpbird', '( %s -> %s e. ( %s [,] %s ) )' % (A0, RP, RA, RB))
ipi = w.s([w.s([pir, w.s([li], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IP)), w.s([ri], 'ltled', '( %s -> %s <_ %s )' % (A0, IP, IB))], '3jca',
                '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (A0, IP, IA, IP, IP, IB)),
           w.s([air, bir, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, IP, IA, IB, IP, IA, IP, IP, IB))],
          'mpbird', '( %s -> %s e. ( %s [,] %s ) )' % (A0, IP, IA, IB))
ppt = w.s([ab, w.s([rpi, ipi], 'jca', '( %s -> ( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) )' % (A0, RP, RA, RB, IP, IA, IB)), w.inst('crectpt')],
          'syl2anc', '( %s -> %s e. ( A crect B ) )' % (A0, PT(RP, IP)))
prect = w.s([w.s([pc, w.inst('replim')], 'syl', '( %s -> P = %s )' % (A0, PT(RP, IP))), ppt], 'eqeltrd', '( %s -> P e. ( A crect B ) )' % A0)
pdm = w.s([rdm, prect], 'sseldd', '( %s -> P e. dom ( CC _D F ) )' % A0)
pd = w.s([rd, prect], 'sseldd', '( %s -> P e. D )' % A0)
ccl = w.s([closed(w, A0, 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), pdm], 'ffvelcdmd', '( %s -> %s e. CC )' % (A0, CDF))
fpc = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
# the extended difference quotient: continuity and holomorphy off P
hol = w.s([fcn, pdm, w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, CDF, CDF))], '3jca',
          '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. dom ( CC _D F ) /\\ %s = %s ) )' % (A0, CDF, CDF))
dcn = w.s([hol, w.inst('dscn')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, DSFC))
dvd = w.s([w.s([fcn, pd, ccl], '3jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D /\\ %s e. CC ) )' % (A0, CDF)), w.inst('dsdv')], 'syl',
          '( %s -> ( dom ( CC _D F ) \\ { P } ) C_ dom ( CC _D %s ) )' % (A0, DSFC))
pss = w.s([w.s([rdm, w.inst('ssdif')], 'syl', '( %s -> %s C_ ( dom ( CC _D F ) \\ { P } ) )' % (A0, PUNC)), dvd], 'sstrd',
          '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, PUNC, DSFC))
gour = w.s([ab, it, w.s([dcn, rd, pss], '3jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, DSFC, PUNC, DSFC)),
            w.inst('rectintgour1')], 'syl3anc', '( %s -> %s = 0 )' % (A0, RINT(DSFC, 'A', 'B')))
# continuity of the two pieces on ( D \ { P } )
epc = w.s([dss, w.inst('ssdif')], 'syl', '( %s -> %s C_ %s )' % (A0, EP, CCP))
g0cn = w.s([pc, epc, w.inst('rinvcnss')], 'syl2anc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, G0, EP))
qcn = w.s([w.s([fcn, pd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D ) )' % A0), w.inst('dsqcn')], 'syl',
          '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, QPF, EP))
pep = w.s([w.s([rd, w.inst('ssdif')], 'syl', '( %s -> %s C_ %s )' % (A0, PUNC, EP))], 'id', '( %s -> %s C_ %s )' % (A0, PUNC, EP)) if False else \
      w.s([rd, w.inst('ssdif')], 'syl', '( %s -> %s C_ %s )' % (A0, PUNC, EP))
# pointwise values on the punctured rectangle
um = w.s([], 'simpr', '( %s -> u e. %s )' % (A1, PUNC))
urect = w.s([um, w.inst('eldifi')], 'syl', '( %s -> u e. ( A crect B ) )' % A1)
une = w.s([w.s([um, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. ( A crect B ) /\\ u =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> u =/= P )' % A1)
ud = w.s([w.s([rd], 'adantr', '( %s -> ( A crect B ) C_ D )' % A1), urect], 'sseldd', '( %s -> u e. D )' % A1)
uc = w.s([w.s([dss], 'adantr', '( %s -> D C_ CC )' % A1), ud], 'sseldd', '( %s -> u e. CC )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
upc = w.s([uc, pc1], 'subcld', '( %s -> ( u - P ) e. CC )' % A1)
upne = w.s([uc, pc1, une], 'subne0d', '( %s -> ( u - P ) =/= 0 )' % A1)
uep = w.s([w.s([ud, une], 'jca', '( %s -> ( u e. D /\\ u =/= P ) )' % A1), w.inst('eldifsn')], 'sylibr', '( %s -> u e. %s )' % (A1, EP))
uccp = w.s([w.s([uc, une], 'jca', '( %s -> ( u e. CC /\\ u =/= P ) )' % A1), w.inst('eldifsn')], 'sylibr', '( %s -> u e. %s )' % (A1, CCP))
fuc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), ud], 'ffvelcdmd', '( %s -> ( F ` u ) e. CC )' % A1)
fpc1 = w.s([fpc], 'adantr', '( %s -> ( F ` P ) e. CC )' % A1)
nuc = w.s([fuc, fpc1], 'subcld', '( %s -> ( ( F ` u ) - ( F ` P ) ) e. CC )' % A1)


def mval(FN, DOM, body, val, memstep, valcl):
    """( A1 -> ( FN ` u ) = val ) by fvmptg"""
    c1 = w.s([], 'oveq1', '( z = u -> ( z - P ) = ( u - P ) )')
    return c1


def fvm(FN, dom, subst, val, memstep, valcl):
    i = w.s(subst + [w.s([], 'eqid', '%s = %s' % (FN, FN))], 'fvmptg',
            '( ( u e. %s /\\ %s e. CC ) -> ( %s ` u ) = %s )' % (dom, val, FN, val))
    return w.s([memstep, valcl, i], 'syl2anc', '( %s -> ( %s ` u ) = %s )' % (A1, FN, val))


s1 = w.s([], 'oveq1', '( z = u -> ( z - P ) = ( u - P ) )')
s2 = w.s([], 'fveq2', '( z = u -> ( F ` z ) = ( F ` u ) )')
sT = w.s([s2, s1], 'oveq12d', '( z = u -> ( ( F ` z ) / ( z - P ) ) = ( ( F ` u ) / ( u - P ) ) )')
sG = w.s([s1], 'oveq2d', '( z = u -> ( 1 / ( z - P ) ) = ( 1 / ( u - P ) ) )')
sQ = w.s([w.s([s2], 'oveq1d', '( z = u -> ( ( F ` z ) - ( F ` P ) ) = ( ( F ` u ) - ( F ` P ) ) )'), s1], 'oveq12d',
         '( z = u -> %s = %s )' % (QUO('z'), QUO('u')))
tvcl = w.s([fuc, upc, upne], 'divcld', '( %s -> ( ( F ` u ) / ( u - P ) ) e. CC )' % A1)
gvcl = w.s([upc, upne], 'reccld', '( %s -> ( 1 / ( u - P ) ) e. CC )' % A1)
qvcl = w.s([nuc, upc, upne], 'divcld', '( %s -> %s e. CC )' % (A1, QUO('u')))
tv = fvm(TGT, PUNC, [sT], '( ( F ` u ) / ( u - P ) )', um, tvcl)
gv = fvm(G0, EP, [sG], '( 1 / ( u - P ) )', uep, gvcl)
qv = fvm(QPF, EP, [sQ], QUO('u'), uep, qvcl)
wv = fvm(RINVF, CCP, [sG], '( 1 / ( u - P ) )', uccp, gvcl)
dv = w.s([w.s([w.s([w.s([fcn], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % A1), w.s([pd], 'adantr', '( %s -> P e. D )' % A1)], 'jca',
                   '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D ) )' % A1),
               w.s([ud, une], 'jca', '( %s -> ( u e. D /\\ u =/= P ) )' % A1)], 'jca',
              '( %s -> ( ( F e. ( D -cn-> CC ) /\\ P e. D ) /\\ ( u e. D /\\ u =/= P ) ) )' % A1), w.inst('dsvaln')], 'syl',
         '( %s -> ( %s ` u ) = %s )' % (A1, DSFC, QUO('u')))
# the three pointwise identities
idg = w.s([gv, wv], 'eqtrd' if False else 'eqtr4d', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (A1, G0, RINVF))
idq = w.s([qv, dv], 'eqtr4d', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (A1, QPF, DSFC))
e1 = w.s([fpc1, upc, upne], 'divrecd', '( %s -> ( ( F ` P ) / ( u - P ) ) = ( ( F ` P ) x. ( 1 / ( u - P ) ) )' % A1 + ' )')
e2 = w.s([fpc1, nuc, upc, upne], 'divdird', '( %s -> ( ( ( F ` P ) + ( ( F ` u ) - ( F ` P ) ) ) / ( u - P ) ) = ( ( ( F ` P ) / ( u - P ) ) + %s ) )' % (A1, QUO('u')))
e3 = w.s([fpc1, fuc, w.inst('pncan3')], 'syl2anc', '( %s -> ( ( F ` P ) + ( ( F ` u ) - ( F ` P ) ) ) = ( F ` u ) )' % A1)
e4 = w.s([w.s([e3], 'oveq1d', '( %s -> ( ( ( F ` P ) + ( ( F ` u ) - ( F ` P ) ) ) / ( u - P ) ) = ( ( F ` u ) / ( u - P ) ) )' % A1)], 'eqcomd',
         '( %s -> ( ( F ` u ) / ( u - P ) ) = ( ( ( F ` P ) + ( ( F ` u ) - ( F ` P ) ) ) / ( u - P ) ) )' % A1)
e5 = w.s([w.s([e4, e2], 'eqtrd', '( %s -> ( ( F ` u ) / ( u - P ) ) = ( ( ( F ` P ) / ( u - P ) ) + %s ) )' % (A1, QUO('u'))),
          w.s([e1], 'oveq1d', '( %s -> ( ( ( F ` P ) / ( u - P ) ) + %s ) = ( ( ( F ` P ) x. ( 1 / ( u - P ) ) ) + %s ) )' % (A1, QUO('u'), QUO('u')))],
         'eqtrd', '( %s -> ( ( F ` u ) / ( u - P ) ) = ( ( ( F ` P ) x. ( 1 / ( u - P ) ) ) + %s ) )' % (A1, QUO('u')))
idt = w.s([w.s([tv, e5], 'eqtrd', '( %s -> ( %s ` u ) = ( ( ( F ` P ) x. ( 1 / ( u - P ) ) ) + %s ) )' % (A1, TGT, QUO('u'))),
           w.s([w.s([gv], 'oveq2d', '( %s -> ( ( F ` P ) x. ( %s ` u ) ) = ( ( F ` P ) x. ( 1 / ( u - P ) ) ) )' % (A1, G0)), qv], 'oveq12d',
               '( %s -> ( ( ( F ` P ) x. ( %s ` u ) ) + ( %s ` u ) ) = ( ( ( F ` P ) x. ( 1 / ( u - P ) ) ) + %s ) )' % (A1, G0, QPF, QUO('u')))],
          'eqtr4d', '( %s -> ( %s ` u ) = ( ( ( F ` P ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A1, TGT, G0, QPF))
alg = w.s([idg], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, PUNC, G0, RINVF))
alq = w.s([idq], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, PUNC, QPF, DSFC))
alt = w.s([idt], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( ( ( F ` P ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A0, PUNC, TGT, G0, QPF))
# sethood
cx = closed(w, A0, 'cnex', 'CC e. _V')
rex = w.s([w.s([ac, bc, w.inst('crectss')], 'syl2anc', '( %s -> ( A crect B ) C_ CC )' % A0)] if False else [], 'id', '') if False else None
rss = w.s([ac, bc, w.inst('crectss')], 'syl2anc', '( %s -> ( A crect B ) C_ CC )' % A0)
rex2 = w.s([cx, rss], 'ssexd', '( %s -> ( A crect B ) e. _V )' % A0)
pex = w.s([rex2, w.inst('difexg')], 'syl', '( %s -> %s e. _V )' % (A0, PUNC))
tex = w.s([pex], 'mptexd', '( %s -> %s e. _V )' % (A0, TGT))
gex = w.s([g0cn, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, G0))
qex = w.s([qcn, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, QPF))
dex = w.s([dcn, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, DSFC))
wex = w.s([w.s([pc, w.inst('rinvcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RINVF, CCP)), w.inst('elex')], 'syl',
          '( %s -> %s e. _V )' % (A0, RINVF))
abi = w.s([ab, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT))
# the linear combination
lc = w.s([abi, w.s([tex, fpc, w.s([g0cn, qcn, pep], '3jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, G0, EP, QPF, EP, PUNC, EP))], '3jca',
               '( %s -> ( %s e. _V /\\ ( F ` P ) e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (A0, TGT, G0, EP, QPF, EP, PUNC, EP)),
           alt, w.inst('rectintlcp')], 'syl3anc',
          '( %s -> %s = ( ( ( F ` P ) x. %s ) + %s ) )' % (A0, RINT(TGT, 'A', 'B'), RINT(G0, 'A', 'B'), RINT(QPF, 'A', 'B')))
eqg = w.s([abi, w.s([gex, wex], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A0, G0, RINVF)), alg, w.inst('rectinteqp')], 'syl3anc',
          '( %s -> %s = %s )' % (A0, RINT(G0, 'A', 'B'), RINT(RINVF, 'A', 'B')))
eqq = w.s([abi, w.s([qex, dex], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A0, QPF, DSFC)), alq, w.inst('rectinteqp')], 'syl3anc',
          '( %s -> %s = %s )' % (A0, RINT(QPF, 'A', 'B'), RINT(DSFC, 'A', 'B')))
wind = w.s([abi, w.inst('rectintwind')], 'syl', '( %s -> %s = %s )' % (A0, RINT(RINVF, 'A', 'B'), TWOPII))
# assemble
r1 = w.s([eqg, wind], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT(G0, 'A', 'B'), TWOPII))
r2 = w.s([eqq, gour], 'eqtrd', '( %s -> %s = 0 )' % (A0, RINT(QPF, 'A', 'B')))
r3 = w.s([w.s([r1], 'oveq2d', '( %s -> ( ( F ` P ) x. %s ) = ( ( F ` P ) x. %s ) )' % (A0, RINT(G0, 'A', 'B'), TWOPII)), r2], 'oveq12d',
         '( %s -> ( ( ( F ` P ) x. %s ) + %s ) = ( ( ( F ` P ) x. %s ) + 0 ) )' % (A0, RINT(G0, 'A', 'B'), RINT(QPF, 'A', 'B'), TWOPII))
ic = closed(w, A0, 'ax-icn', '_i e. CC'); pic = closed(w, A0, 'picn', '_pi e. CC')
t2c = closed(w, A0, '2cn', '2 e. CC')
tpc = w.s([t2c, w.s([ic, pic], 'mulcld', '( %s -> %s e. CC )' % (A0, IPI))], 'mulcld', '( %s -> %s e. CC )' % (A0, TWOPII))
r4 = w.s([w.s([fpc, tpc], 'mulcld', '( %s -> ( ( F ` P ) x. %s ) e. CC )' % (A0, TWOPII))], 'addridd',
         '( %s -> ( ( ( F ` P ) x. %s ) + 0 ) = ( ( F ` P ) x. %s ) )' % (A0, TWOPII, TWOPII))
r5 = w.s([fpc, tpc], 'mulcomd', '( %s -> ( ( F ` P ) x. %s ) = ( %s x. ( F ` P ) ) )' % (A0, TWOPII, TWOPII))
w.qed([lc, w.s([w.s([r3, r4], 'eqtrd', '( %s -> ( ( ( F ` P ) x. %s ) + %s ) = ( ( F ` P ) x. %s ) )' % (A0, RINT(G0, 'A', 'B'), RINT(QPF, 'A', 'B'), TWOPII)), r5],
               'eqtrd', '( %s -> ( ( ( F ` P ) x. %s ) + %s ) = ( %s x. ( F ` P ) ) )' % (A0, RINT(G0, 'A', 'B'), RINT(QPF, 'A', 'B'), TWOPII))],
      'eqtrd', '( %s -> %s = ( %s x. ( F ` P ) ) )' % (A0, RINT(TGT, 'A', 'B'), TWOPII)); run(w)
