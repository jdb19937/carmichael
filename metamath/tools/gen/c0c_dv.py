"""Sortie C0c batch 9: the holomorphy of the extended difference quotient off
the base point."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

CCP = '( CC \\ { P } )'
CC0 = '( CC \\ { 0 } )'
RINVF = '( z e. %s |-> ( 1 / ( z - P ) ) )' % CCP
DRINVF = '( z e. %s |-> -u ( 1 / ( ( z - P ) ^ 2 ) ) )' % CCP
EP = '( D \\ { P } )'
QUO = lambda X: '( ( ( F ` %s ) - ( F ` P ) ) / ( %s - P ) )' % (X, X)
DSF = '( z e. D |-> if ( z = P , C , %s ) )' % QUO('z')
QPF = '( z e. %s |-> %s )' % (EP, QUO('z'))
FP = '( F e. ( D -cn-> CC ) /\\ P e. D )'
JCC = '( %s |`t CC )' % TOP

# ---- cnopnsn: the punctured plane is open
w = W('cnopnsn', 'The complex plane with one point removed is open.')
A0 = 'P e. CC'
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
hau = w.s([ej], 'cnfldhaus', '%s e. Haus' % TOP)
uni = w.s([], 'unicntop', 'CC = U. %s' % TOP)
scl = w.s([uni], 'sncld', '( ( %s e. Haus /\\ P e. CC ) -> { P } e. ( Clsd ` %s ) )' % (TOP, TOP))
cl = w.s([w.s([hau], 'a1i', '( %s -> %s e. Haus )' % (A0, TOP)), w.s([], 'id', '( %s -> P e. CC )' % A0), scl], 'syl2anc',
         '( %s -> { P } e. ( Clsd ` %s ) )' % (A0, TOP))
op = w.s([uni], 'cldopn', '( { P } e. ( Clsd ` %s ) -> ( CC \\ { P } ) e. %s )' % (TOP, TOP))
w.qed([cl, op], 'syl', '( %s -> %s e. %s )' % (A0, CCP, TOP)); run(w)

# ---- cnopnsnr: the punctured plane is open in the relative topology on CC
w = W('cnopnsnr', 'The complex plane with one point removed is open in the subspace topology on the complex numbers.')
A0 = 'P e. CC'
uni = w.s([], 'unicntop', 'CC = U. %s' % TOP)
tex = w.s([], 'fvex', '%s e. _V' % TOP)
rid = w.s([tex, w.s([uni], 'restid', '( %s e. _V -> %s = %s )' % (TOP, JCC, TOP))], 'ax-mp', '%s = %s' % (JCC, TOP))
op = w.s([], 'cnopnsn', '( %s -> %s e. %s )' % (A0, CCP, TOP))
w.qed([w.s([], 'id', '( %s -> P e. CC )' % A0), w.s([w.s([op], 'imp' if False else 'id', '( %s -> ( %s -> %s e. %s ) )' % (A0, A0, CCP, TOP)) if False else op,
        w.s([rid], 'eqcomi', '%s = %s' % (TOP, JCC))], 'syl6eleq' if False else 'eleqtrdi', '( %s -> %s e. %s )' % (A0, CCP, JCC))], 'mpi' if False else 'pm2.43i',
      '( %s -> %s e. %s )' % (A0, CCP, JCC)) if False else None
w.lines = []
w.n = 0
uni = w.s([], 'unicntop', 'CC = U. %s' % TOP)
tex = w.s([], 'fvex', '%s e. _V' % TOP)
rid = w.s([tex, w.s([uni], 'restid', '( %s e. _V -> %s = %s )' % (TOP, JCC, TOP))], 'ax-mp', '%s = %s' % (JCC, TOP))
ridc = w.s([rid], 'eqcomi', '%s = %s' % (TOP, JCC))
op = w.s([w.s([], 'id', '( %s -> P e. CC )' % A0), w.inst('cnopnsn')], 'syl', '( %s -> %s e. %s )' % (A0, CCP, TOP))
w.qed([op, w.s([ridc], 'a1i', '( %s -> %s = %s )' % (A0, TOP, JCC))], 'eleqtrd', '( %s -> %s e. %s )' % (A0, CCP, JCC)); run(w)

# ---- dvrinv: the derivative of 1 / ( z - P ) off P
w = W('dvrinv', 'The derivative of 1 / ( z - P ) on the complex plane with P removed.')
A0 = 'P e. CC'
A1 = '( %s /\\ z e. CC )' % A0
A2 = '( %s /\\ z e. %s )' % (A0, CCP)
pc = w.s([], 'id', '( %s -> P e. CC )' % A0)
ccp = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
c1 = closed(w, A0, 'ax-1cn', '1 e. CC')
c0 = w.s([], '0cnd', '( %s -> 0 e. CC )' % A0)
# derivative of the constant 1 and of z - P on all of CC
d1 = w.s([ccp, c1], 'dvmptc', '( %s -> ( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 ) )' % A0)
did = w.s([ccp], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
zc1 = w.s([], 'simpr', '( %s -> z e. CC )' % A1)
c11 = w.s([c1], 'adantr', '( %s -> 1 e. CC )' % A1)
c01 = w.s([c0], 'adantr', '( %s -> 0 e. CC )' % A1)
dpc = w.s([ccp, pc], 'dvmptc', '( %s -> ( CC _D ( z e. CC |-> P ) ) = ( z e. CC |-> 0 ) )' % A0)
dsb = w.s([ccp, zc1, c11, did, pc1, c01, dpc], 'dvmptsub', '( %s -> ( CC _D ( z e. CC |-> ( z - P ) ) ) = ( z e. CC |-> ( 1 - 0 ) ) )' % A0)
m10 = w.s([], '1m0e1', '( 1 - 0 ) = 1')
dsb2 = w.s([dsb, w.s([w.s([m10], 'a1i', '( %s -> ( 1 - 0 ) = 1 )' % A1)], 'mpteq2dva', '( %s -> ( z e. CC |-> ( 1 - 0 ) ) = ( z e. CC |-> 1 ) )' % A0)],
           'eqtrd', '( %s -> ( CC _D ( z e. CC |-> ( z - P ) ) ) = ( z e. CC |-> 1 ) )' % A0)
# restrict both to the punctured plane
ss = closed(w, A0, 'difss', '%s C_ CC' % CCP)
ej = w.s([], 'eqid', '%s = %s' % (JCC, JCC))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
opn = w.s([pc, w.inst('cnopnsnr')], 'syl', '( %s -> %s e. %s )' % (A0, CCP, JCC))
dr1 = w.s([ccp, c11, c01, d1, ss, ej, ek, opn], 'dvmptres', '( %s -> ( CC _D ( z e. %s |-> 1 ) ) = ( z e. %s |-> 0 ) )' % (A0, CCP, CCP))
zpc1 = w.s([zc1, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
dr2 = w.s([ccp, zpc1, c11, dsb2, ss, ej, ek, opn], 'dvmptres', '( %s -> ( CC _D ( z e. %s |-> ( z - P ) ) ) = ( z e. %s |-> 1 ) )' % (A0, CCP, CCP))
# dvmptdiv
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A2, CCP))
zc2 = w.s([zm, w.inst('eldifi')], 'syl', '( %s -> z e. CC )' % A2)
pc2 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A2)
zne2 = w.s([w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A2), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A2)
zpc2 = w.s([zc2, pc2], 'subcld', '( %s -> ( z - P ) e. CC )' % A2)
zpne2 = w.s([zc2, pc2, zne2], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A2)
zp0 = w.s([w.s([zpc2, zpne2], 'jca', '( %s -> ( ( z - P ) e. CC /\\ ( z - P ) =/= 0 ) )' % A2), w.inst('eldifsn')], 'sylibr',
          '( %s -> ( z - P ) e. %s )' % (A2, CC0))
c12 = w.s([c1], 'adantr', '( %s -> 1 e. CC )' % A2)
c02 = w.s([c0], 'adantr', '( %s -> 0 e. CC )' % A2)
RAWD = '( ( ( 0 x. ( z - P ) ) - ( 1 x. 1 ) ) / ( ( z - P ) ^ 2 ) )'
dq = w.s([ccp, c12, c02, dr1, zp0, c12, dr2], 'dvmptdiv', '( %s -> ( CC _D %s ) = ( z e. %s |-> %s ) )' % (A0, RINVF, CCP, RAWD))
# simplify the numerator
n1 = w.s([zpc2], 'mul02d', '( %s -> ( 0 x. ( z - P ) ) = 0 )' % A2)
n2 = w.s([c12], 'mullidd', '( %s -> ( 1 x. 1 ) = 1 )' % A2)
n3 = w.s([n1, n2], 'oveq12d', '( %s -> ( ( 0 x. ( z - P ) ) - ( 1 x. 1 ) ) = ( 0 - 1 ) )' % A2)
n4 = w.s([], 'df-neg', '-u 1 = ( 0 - 1 )')
n5 = w.s([n3, w.s([w.s([n4], 'eqcomi', '( 0 - 1 ) = -u 1')], 'a1i', '( %s -> ( 0 - 1 ) = -u 1 )' % A2)], 'eqtrd',
         '( %s -> ( ( 0 x. ( z - P ) ) - ( 1 x. 1 ) ) = -u 1 )' % A2)
sq = w.s([zpc2, w.s([], '2nn0', '2 e. NN0'), zpne2] if False else [zpc2, zpne2], 'sqne0d' if False else 'jca', '') if False else None
sqc = w.s([zpc2, w.s([], '2z', '2 e. ZZ')] if False else [zpc2], 'sqcld', '( %s -> ( ( z - P ) ^ 2 ) e. CC )' % A2)
sqne = w.s([zpne2, w.s([zpc2, w.inst('sqne0')], 'syl', '( %s -> ( ( ( z - P ) ^ 2 ) =/= 0 <-> ( z - P ) =/= 0 ) )' % A2)], 'mpbird',
           '( %s -> ( ( z - P ) ^ 2 ) =/= 0 )' % A2)
n6 = w.s([n5], 'oveq1d', '( %s -> %s = ( -u 1 / ( ( z - P ) ^ 2 ) ) )' % (A2, RAWD))
n7 = w.s([c12, sqc, sqne], 'divnegd' if False else 'divnegd', '( %s -> -u ( 1 / ( ( z - P ) ^ 2 ) ) = ( -u 1 / ( ( z - P ) ^ 2 ) ) )' % A2)
n8 = w.s([n6, w.s([n7], 'eqcomd', '( %s -> ( -u 1 / ( ( z - P ) ^ 2 ) ) = -u ( 1 / ( ( z - P ) ^ 2 ) ) )' % A2)], 'eqtrd',
         '( %s -> %s = -u ( 1 / ( ( z - P ) ^ 2 ) ) )' % (A2, RAWD))
mp = w.s([n8], 'mpteq2dva', '( %s -> ( z e. %s |-> %s ) = %s )' % (A0, CCP, RAWD, DRINVF))
w.qed([dq, mp], 'eqtrd', '( %s -> ( CC _D %s ) = %s )' % (A0, RINVF, DRINVF)); run(w)

# ---- cnrestid: the subspace topology of CC in itself
w = W('cnrestid', 'The subspace topology induced on the complex numbers by the standard topology is that topology.')
uni = w.s([], 'unicntop', 'CC = U. %s' % TOP)
tex = w.s([], 'fvex', '%s e. _V' % TOP)
w.qed([tex, w.s([uni], 'restid', '( %s e. _V -> %s = %s )' % (TOP, JCC, TOP))], 'ax-mp', '%s = %s' % (JCC, TOP)); run(w)

ANT = '( %s /\\ ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % FP
INTEP = '( ( int ` %s ) ` %s )' % (TOP, EP)
N1 = '( z e. %s |-> ( ( F ` z ) - ( F ` P ) ) )' % EP
G1 = '( z e. %s |-> ( 1 / ( z - P ) ) )' % EP
CONST = '( %s X. { -u ( F ` P ) } )' % EP


def base(w, A0):
    """the standing context of ANT"""
    d = {}
    d['fcn'] = fcn = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, FP)), w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    d['pd'] = pd = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, FP)), w.inst('simpr')], 'syl', '( %s -> P e. D )' % A0)
    d['xdm'] = w.s([w.s([], 'simpr', '( %s -> ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % A0), w.inst('simpl')], 'syl', '( %s -> X e. dom ( CC _D F ) )' % A0)
    d['xne'] = w.s([w.s([], 'simpr', '( %s -> ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % A0), w.inst('simpr')], 'syl', '( %s -> X =/= P )' % A0)
    d['dss'] = dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    d['ff'] = ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    d['ccs'] = ccs = closed(w, A0, 'ssid', 'CC C_ CC')
    d['epd'] = epd = closed(w, A0, 'difss', '%s C_ D' % EP)
    d['epc'] = w.s([epd, dss], 'sstrd', '( %s -> %s C_ CC )' % (A0, EP))
    d['xd'] = xd = w.s([w.s([ccs, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0), d['xdm']], 'sseldd', '( %s -> X e. D )' % A0)
    d['xc'] = w.s([dss, xd], 'sseldd', '( %s -> X e. CC )' % A0)
    d['xep'] = w.s([w.s([xd, d['xne']], 'jca', '( %s -> ( X e. D /\\ X =/= P ) )' % A0), w.inst('eldifsn')], 'sylibr', '( %s -> X e. %s )' % (A0, EP))
    d['pc'] = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
    d['fpc'] = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
    d['top'] = closed(w, A0, 'cnfldtop', '%s e. Top' % TOP)
    d['uni'] = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    d['ej'] = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    d['et'] = w.s([w.s([], 'cnrestid', '%s = %s' % (JCC, TOP))], 'eqcomi', '%s = %s' % (TOP, JCC))
    return d


# ---- dsdv1: a differentiability point off P is interior to the punctured domain
w = W('dsdv1', 'A point at which a function is differentiable, other than the base point, is interior to the punctured domain.')
A0 = ANT
d = base(w, A0)
ntd = w.s([d['ccs'], d['ff'], d['dss'], d['et'], d['ej'], w.inst('dvbssntr')] if False else
          [d['ccs'], d['ff'], d['dss'], d['et'], d['ej']], 'dvbssntr', '( %s -> dom ( CC _D F ) C_ ( ( int ` %s ) ` D ) )' % (A0, TOP))
xint = w.s([ntd, d['xdm']], 'sseldd', '( %s -> X e. ( ( int ` %s ) ` D ) )' % (A0, TOP))
ntop = w.s([d['top'], d['dss'], w.s([d['uni']], 'ntropn', '( ( %s e. Top /\\ D C_ CC ) -> ( ( int ` %s ) ` D ) e. %s )' % (TOP, TOP, TOP))], 'syl2anc',
           '( %s -> ( ( int ` %s ) ` D ) e. %s )' % (A0, TOP, TOP))
pop = w.s([d['pc'], w.inst('cnopnsn')], 'syl', '( %s -> ( CC \\ { P } ) e. %s )' % (A0, TOP))
O = '( ( ( int ` %s ) ` D ) i^i ( CC \\ { P } ) )' % TOP
oop = w.s([d['top'], ntop, pop, w.inst('inopn')], 'syl3anc', '( %s -> %s e. %s )' % (A0, O, TOP))
xccp = w.s([w.s([d['xc'], d['xne']], 'jca', '( %s -> ( X e. CC /\\ X =/= P ) )' % A0), w.inst('eldifsn')], 'sylibr', '( %s -> X e. ( CC \\ { P } ) )' % A0)
xo = w.s([xint, xccp], 'elind', '( %s -> X e. %s )' % (A0, O))
# O C_ ( D \ { P } )
A1 = '( %s /\\ g e. %s )' % (A0, O)
gm = w.s([], 'simpr', '( %s -> g e. %s )' % (A1, O))
gint = w.s([gm], 'elin1d', '( %s -> g e. ( ( int ` %s ) ` D ) )' % (A1, TOP))
gccp = w.s([gm], 'elin2d', '( %s -> g e. ( CC \\ { P } ) )' % A1)
nss = w.s([w.s([d['top']], 'adantr', '( %s -> %s e. Top )' % (A1, TOP)), w.s([d['dss']], 'adantr', '( %s -> D C_ CC )' % A1),
           w.s([d['uni']], 'ntrss2', '( ( %s e. Top /\\ D C_ CC ) -> ( ( int ` %s ) ` D ) C_ D )' % (TOP, TOP))], 'syl2anc',
          '( %s -> ( ( int ` %s ) ` D ) C_ D )' % (A1, TOP))
gd = w.s([nss, gint], 'sseldd', '( %s -> g e. D )' % A1)
gne = w.s([w.s([gccp, w.inst('eldifsn')], 'sylib', '( %s -> ( g e. CC /\\ g =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> g =/= P )' % A1)
gep = w.s([w.s([gd, gne], 'jca', '( %s -> ( g e. D /\\ g =/= P ) )' % A1), w.inst('eldifsn')], 'sylibr', '( %s -> g e. %s )' % (A1, EP))
oss = w.s([w.s([gep], 'ex', '( %s -> ( g e. %s -> g e. %s ) )' % (A0, O, EP))], 'ssrdv', '( %s -> %s C_ %s )' % (A0, O, EP))
sn = w.s([w.s([d['top'], d['epc']], 'jca', '( %s -> ( %s e. Top /\\ %s C_ CC ) )' % (A0, TOP, EP)), w.s([oop, oss], 'jca', '( %s -> ( %s e. %s /\\ %s C_ %s ) )' % (A0, O, TOP, O, EP)),
           w.s([d['uni']], 'ssntr', '( ( ( %s e. Top /\\ %s C_ CC ) /\\ ( %s e. %s /\\ %s C_ %s ) ) -> %s C_ %s )' % (TOP, EP, O, TOP, O, EP, O, INTEP))],
          'syl2anc', '( %s -> %s C_ %s )' % (A0, O, INTEP))
w.qed([sn, xo], 'sseldd', '( %s -> X e. %s )' % (A0, INTEP)); run(w)

# ---- dsdv3: the reciprocal factor is differentiable at X
w = W('dsdv3', 'The factor 1 / ( z - P ) is differentiable at every point of the punctured domain.')
A0 = ANT
A1 = '( %s /\\ z e. %s )' % (A0, CCP)
d = base(w, A0)
riv = w.s([d['pc'], w.inst('rinvcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RINVF, CCP))
rf = w.s([riv, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (A0, RINVF, CCP))
ccpc = closed(w, A0, 'difss', '%s C_ CC' % CCP)
epccp = w.s([d['dss'], w.inst('ssdif')], 'syl', '( %s -> %s C_ %s )' % (A0, EP, CCP))
g1eq = w.s([epccp, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, RINVF, EP, G1))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
dvr = w.s([w.s([w.s([d['ccs'], rf], 'jca', '( %s -> ( CC C_ CC /\\ %s : %s --> CC ) )' % (A0, RINVF, CCP)),
                w.s([ccpc, d['epc']], 'jca', '( %s -> ( %s C_ CC /\\ %s C_ CC ) )' % (A0, CCP, EP))], 'jca',
               '( %s -> ( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) ) )' % (A0, RINVF, CCP, CCP, EP)),
           w.s([ek, d['et']], 'dvres', '( ( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (RINVF, CCP, CCP, EP, RINVF, EP, RINVF, INTEP))],
          'syl', '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (A0, RINVF, EP, RINVF, INTEP))
# dom ( CC _D RINVF ) = CCP
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, CCP))
zc = w.s([zm, w.inst('eldifi')], 'syl', '( %s -> z e. CC )' % A1)
pc1 = w.s([d['pc']], 'adantr', '( %s -> P e. CC )' % A1)
zne = w.s([w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
zpc = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
zpne = w.s([zc, pc1, zne], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
sqc = w.s([zpc], 'sqcld', '( %s -> ( ( z - P ) ^ 2 ) e. CC )' % A1)
sqne = w.s([zpne, w.s([zpc, w.inst('sqne0')], 'syl', '( %s -> ( ( ( z - P ) ^ 2 ) =/= 0 <-> ( z - P ) =/= 0 ) )' % A1)], 'mpbird',
           '( %s -> ( ( z - P ) ^ 2 ) =/= 0 )' % A1)
vcl = w.s([w.s([sqc, sqne], 'reccld', '( %s -> ( 1 / ( ( z - P ) ^ 2 ) ) e. CC )' % A1)], 'negcld',
          '( %s -> -u ( 1 / ( ( z - P ) ^ 2 ) ) e. CC )' % A1)
drf = w.s([vcl, w.s([], 'eqid', '%s = %s' % (DRINVF, DRINVF))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, DRINVF, CCP))
ddom = w.s([w.s([w.s([d['pc'], w.inst('dvrinv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, RINVF, DRINVF))], 'dmeqd',
                '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, RINVF, DRINVF)),
            w.s([drf, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A0, DRINVF, CCP))], 'eqtrd',
           '( %s -> dom ( CC _D %s ) = %s )' % (A0, RINVF, CCP))
xccp = w.s([w.s([d['xc'], d['xne']], 'jca', '( %s -> ( X e. CC /\\ X =/= P ) )' % A0), w.inst('eldifsn')], 'sylibr', '( %s -> X e. %s )' % (A0, CCP))
xdmr = w.s([xccp, ddom], 'eleqtrrd', '( %s -> X e. dom ( CC _D %s ) )' % (A0, RINVF))
fun = w.s([w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (RINVF, RINVF)), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D %s )' % RINVF)
br = w.s([xdmr, w.s([w.s([fun], 'a1i', '( %s -> Fun ( CC _D %s ) )' % (A0, RINVF)), w.inst('funfvbrb')], 'syl',
                    '( %s -> ( X e. dom ( CC _D %s ) <-> X ( CC _D %s ) ( ( CC _D %s ) ` X ) ) )' % (A0, RINVF, RINVF, RINVF))], 'mpbid',
         '( %s -> X ( CC _D %s ) ( ( CC _D %s ) ` X ) )' % (A0, RINVF, RINVF))
vex = w.s([], 'fvexd', '( %s -> ( ( CC _D %s ) ` X ) e. _V )' % (A0, RINVF))
xint = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, FP)), w.s([], 'simpr', '( %s -> ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % A0), w.inst('dsdv1')],
           'syl2anc', '( %s -> X e. %s )' % (A0, INTEP))
brr = w.s([xint, br, w.s([vex, w.inst('brres')], 'syl',
                         '( %s -> ( X ( ( CC _D %s ) |` %s ) ( ( CC _D %s ) ` X ) <-> ( X e. %s /\\ X ( CC _D %s ) ( ( CC _D %s ) ` X ) ) ) )' % (A0, RINVF, INTEP, RINVF, INTEP, RINVF, RINVF))],
          'mpbir2and', '( %s -> X ( ( CC _D %s ) |` %s ) ( ( CC _D %s ) ` X ) )' % (A0, RINVF, INTEP, RINVF))
b2 = w.s([brr, w.s([dvr], 'breqd', '( %s -> ( X ( CC _D ( %s |` %s ) ) ( ( CC _D %s ) ` X ) <-> X ( ( CC _D %s ) |` %s ) ( ( CC _D %s ) ` X ) ) )' % (A0, RINVF, EP, RINVF, RINVF, INTEP, RINVF))],
         'mpbird', '( %s -> X ( CC _D ( %s |` %s ) ) ( ( CC _D %s ) ` X ) )' % (A0, RINVF, EP, RINVF))
w.qed([b2, w.s([w.s([g1eq], 'dveq2d' if False else 'oveq2d', '( %s -> ( CC _D ( %s |` %s ) ) = ( CC _D %s ) )' % (A0, RINVF, EP, G1))], 'breqd',
               '( %s -> ( X ( CC _D ( %s |` %s ) ) ( ( CC _D %s ) ` X ) <-> X ( CC _D %s ) ( ( CC _D %s ) ` X ) ) )' % (A0, RINVF, EP, RINVF, G1, RINVF))],
      'mpbid', '( %s -> X ( CC _D %s ) ( ( CC _D %s ) ` X ) )' % (A0, G1, RINVF)); run(w)

FE = '( F |` %s )' % EP
CCC = '( CC X. { -u ( F ` P ) } )'
KX = '( ( CC _D F ) ` X )'

# ---- dsdv2: the numerator is differentiable at X
w = W('dsdv2', 'The numerator of the difference quotient is differentiable wherever the function is.')
A0 = ANT
A1 = '( %s /\\ z e. %s )' % (A0, EP)
d = base(w, A0)
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
xint = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, FP)), w.s([], 'simpr', '( %s -> ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % A0), w.inst('dsdv1')],
           'syl2anc', '( %s -> X e. %s )' % (A0, INTEP))
fef = w.s([d['ff'], d['epd'], w.inst('fssres')], 'syl2anc', '( %s -> %s : %s --> CC )' % (A0, FE, EP))
dvrF = w.s([w.s([w.s([d['ccs'], d['ff']], 'jca', '( %s -> ( CC C_ CC /\\ F : D --> CC ) )' % A0),
                 w.s([d['dss'], d['epc']], 'jca', '( %s -> ( D C_ CC /\\ %s C_ CC ) )' % (A0, EP))], 'jca',
                '( %s -> ( ( CC C_ CC /\\ F : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) )' % (A0, EP)),
            w.s([ek, d['et']], 'dvres', '( ( ( CC C_ CC /\\ F : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) -> ( CC _D %s ) = ( ( CC _D F ) |` %s ) )' % (EP, FE, INTEP))],
           'syl', '( %s -> ( CC _D %s ) = ( ( CC _D F ) |` %s ) )' % (A0, FE, INTEP))
funF = w.s([w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D F )')
brF = w.s([d['xdm'], w.s([w.s([funF], 'a1i', '( %s -> Fun ( CC _D F ) )' % A0), w.inst('funfvbrb')], 'syl',
                         '( %s -> ( X e. dom ( CC _D F ) <-> X ( CC _D F ) %s ) )' % (A0, KX))], 'mpbid', '( %s -> X ( CC _D F ) %s )' % (A0, KX))
kex = w.s([], 'fvexd', '( %s -> %s e. _V )' % (A0, KX))
brFr = w.s([xint, brF, w.s([kex, w.inst('brres')], 'syl',
                           '( %s -> ( X ( ( CC _D F ) |` %s ) %s <-> ( X e. %s /\\ X ( CC _D F ) %s ) ) )' % (A0, INTEP, KX, INTEP, KX))],
           'mpbir2and', '( %s -> X ( ( CC _D F ) |` %s ) %s )' % (A0, INTEP, KX))
brFE = w.s([brFr, w.s([dvrF], 'breqd', '( %s -> ( X ( CC _D %s ) %s <-> X ( ( CC _D F ) |` %s ) %s ) )' % (A0, FE, KX, INTEP, KX))], 'mpbird',
           '( %s -> X ( CC _D %s ) %s )' % (A0, FE, KX))
# the constant function
nfp = w.s([d['fpc']], 'negcld', '( %s -> -u ( F ` P ) e. CC )' % A0)
snss = w.s([nfp, w.inst('snssi')], 'syl', '( %s -> { -u ( F ` P ) } C_ CC )' % A0)
cf0 = w.s([w.s([nfp, w.inst('fconstg')], 'syl', '( %s -> %s : CC --> { -u ( F ` P ) } )' % (A0, CCC)), snss], 'fssd',
          '( %s -> %s : CC --> CC )' % (A0, CCC))
dvc = w.s([nfp, w.inst('dvconst')], 'syl', '( %s -> ( CC _D %s ) = ( CC X. { 0 } ) )' % (A0, CCC))
dvrC = w.s([w.s([w.s([d['ccs'], cf0], 'jca', '( %s -> ( CC C_ CC /\\ %s : CC --> CC ) )' % (A0, CCC)),
                 w.s([d['ccs'], d['epc']], 'jca', '( %s -> ( CC C_ CC /\\ %s C_ CC ) )' % (A0, EP))], 'jca',
                '( %s -> ( ( CC C_ CC /\\ %s : CC --> CC ) /\\ ( CC C_ CC /\\ %s C_ CC ) ) )' % (A0, CCC, EP)),
            w.s([ek, d['et']], 'dvres', '( ( ( CC C_ CC /\\ %s : CC --> CC ) /\\ ( CC C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (CCC, EP, CCC, EP, CCC, INTEP))],
           'syl', '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (A0, CCC, EP, CCC, INTEP))
xpr = w.s([d['epc'], w.inst('xpssres')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, CCC, EP, CONST))
dvrC2 = w.s([w.s([w.s([xpr], 'oveq2d', '( %s -> ( CC _D ( %s |` %s ) ) = ( CC _D %s ) )' % (A0, CCC, EP, CONST))], 'eqcomd',
                 '( %s -> ( CC _D %s ) = ( CC _D ( %s |` %s ) ) )' % (A0, CONST, CCC, EP)),
             w.s([dvrC, w.s([dvc], 'reseq1d', '( %s -> ( ( CC _D %s ) |` %s ) = ( ( CC X. { 0 } ) |` %s ) )' % (A0, CCC, INTEP, INTEP))], 'eqtrd',
                 '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC X. { 0 } ) |` %s ) )' % (A0, CCC, EP, INTEP))], 'eqtrd',
            '( %s -> ( CC _D %s ) = ( ( CC X. { 0 } ) |` %s ) )' % (A0, CONST, INTEP))
z0v = closed(w, A0, 'c0ex', '0 e. _V')
z0s = w.s([z0v, w.inst('snidg')], 'syl', '( %s -> 0 e. { 0 } )' % A0)
brx = w.s([w.s([d['xc'], z0s], 'jca', '( %s -> ( X e. CC /\\ 0 e. { 0 } ) )' % A0), w.inst('brxp')], 'sylibr', '( %s -> X ( CC X. { 0 } ) 0 )' % A0)
brxr = w.s([xint, brx, w.s([z0v, w.inst('brres')], 'syl',
                           '( %s -> ( X ( ( CC X. { 0 } ) |` %s ) 0 <-> ( X e. %s /\\ X ( CC X. { 0 } ) 0 ) ) )' % (A0, INTEP, INTEP))],
           'mpbir2and', '( %s -> X ( ( CC X. { 0 } ) |` %s ) 0 )' % (A0, INTEP))
brC = w.s([brxr, w.s([dvrC2], 'breqd', '( %s -> ( X ( CC _D %s ) 0 <-> X ( ( CC X. { 0 } ) |` %s ) 0 ) )' % (A0, CONST, INTEP))], 'mpbird',
          '( %s -> X ( CC _D %s ) 0 )' % (A0, CONST))
conf = w.s([w.s([nfp, w.inst('fconstg')], 'syl', '( %s -> %s : %s --> { -u ( F ` P ) } )' % (A0, CONST, EP)), snss], 'fssd',
           '( %s -> %s : %s --> CC )' % (A0, CONST, EP))
add = w.s([fef, d['epc'], conf, d['epc'], d['ccs'], brFE, brC, ek], 'dvaddbr',
          '( %s -> X ( CC _D ( %s oF + %s ) ) ( %s + 0 ) )' % (A0, FE, CONST, KX))
# identify the sum function
dex = w.s([d['dss'], closed(w, A0, 'cnex', 'CC e. _V')], 'ssexd' if False else 'ssexd', '( %s -> D e. _V )' % A0)
epex = w.s([dex, w.inst('difexg')], 'syl', '( %s -> %s e. _V )' % (A0, EP))
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, EP))
zd = w.s([w.s([d['epd']], 'adantr', '( %s -> %s C_ D )' % (A1, EP)), zm], 'sseldd', '( %s -> z e. D )' % A1)
fzc = w.s([w.s([d['ff']], 'adantr', '( %s -> F : D --> CC )' % A1), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
nfp1 = w.s([nfp], 'adantr', '( %s -> -u ( F ` P ) e. CC )' % A1)
fmp = w.s([d['ff']], 'feqmptd', '( %s -> F = ( z e. D |-> ( F ` z ) ) )' % A0)
fer = w.s([w.s([fmp], 'reseq1d', '( %s -> %s = ( ( z e. D |-> ( F ` z ) ) |` %s ) )' % (A0, FE, EP)),
           w.s([d['epd'], w.inst('resmpt')], 'syl', '( %s -> ( ( z e. D |-> ( F ` z ) ) |` %s ) = ( z e. %s |-> ( F ` z ) ) )' % (A0, EP, EP))],
          'eqtrd', '( %s -> %s = ( z e. %s |-> ( F ` z ) ) )' % (A0, FE, EP))
cmp = closed(w, A0, 'fconstmpt', '%s = ( z e. %s |-> -u ( F ` P ) )' % (CONST, EP))
off = w.s([epex, fzc, nfp1, fer, cmp], 'offval2', '( %s -> ( %s oF + %s ) = ( z e. %s |-> ( ( F ` z ) + -u ( F ` P ) ) ) )' % (A0, FE, CONST, EP))
neg = w.s([fzc, w.s([d['fpc']], 'adantr', '( %s -> ( F ` P ) e. CC )' % A1)], 'negsubd',
          '( %s -> ( ( F ` z ) + -u ( F ` P ) ) = ( ( F ` z ) - ( F ` P ) ) )' % A1)
off2 = w.s([off, w.s([neg], 'mpteq2dva', '( %s -> ( z e. %s |-> ( ( F ` z ) + -u ( F ` P ) ) ) = %s )' % (A0, EP, N1))], 'eqtrd',
           '( %s -> ( %s oF + %s ) = %s )' % (A0, FE, CONST, N1))
w.qed([add, w.s([w.s([off2], 'oveq2d', '( %s -> ( CC _D ( %s oF + %s ) ) = ( CC _D %s ) )' % (A0, FE, CONST, N1))], 'breqd',
                '( %s -> ( X ( CC _D ( %s oF + %s ) ) ( %s + 0 ) <-> X ( CC _D %s ) ( %s + 0 ) ) )' % (A0, FE, CONST, KX, N1, KX))],
      'mpbid', '( %s -> X ( CC _D %s ) ( %s + 0 ) )' % (A0, N1, KX)); run(w)

QPF = '( z e. %s |-> %s )' % (EP, QUO('z'))
LX = '( ( CC _D %s ) ` X )' % RINVF
VAL = '( ( ( %s + 0 ) x. ( %s ` X ) ) + ( %s x. ( %s ` X ) ) )' % (KX, G1, LX, N1)

# ---- dsdv4: the difference quotient is differentiable at X
w = W('dsdv4', 'The difference quotient is differentiable at every point off the base point where the function is.')
A0 = ANT
A1 = '( %s /\\ z e. %s )' % (A0, EP)
d = base(w, A0)
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, EP))
zd = w.s([w.s([d['epd']], 'adantr', '( %s -> %s C_ D )' % (A1, EP)), zm], 'sseldd', '( %s -> z e. D )' % A1)
zne = w.s([w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. D /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
zc = w.s([w.s([d['dss']], 'adantr', '( %s -> D C_ CC )' % A1), zd], 'sseldd', '( %s -> z e. CC )' % A1)
pc1 = w.s([d['pc']], 'adantr', '( %s -> P e. CC )' % A1)
zpc = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
zpne = w.s([zc, pc1, zne], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
fzc = w.s([w.s([d['ff']], 'adantr', '( %s -> F : D --> CC )' % A1), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
nc = w.s([fzc, w.s([d['fpc']], 'adantr', '( %s -> ( F ` P ) e. CC )' % A1)], 'subcld', '( %s -> ( ( F ` z ) - ( F ` P ) ) e. CC )' % A1)
rc = w.s([zpc, zpne], 'reccld', '( %s -> ( 1 / ( z - P ) ) e. CC )' % A1)
n1f = w.s([nc, w.s([], 'eqid', '%s = %s' % (N1, N1))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, N1, EP))
g1f = w.s([rc, w.s([], 'eqid', '%s = %s' % (G1, G1))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, G1, EP))
bf = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, FP)), w.s([], 'simpr', '( %s -> ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % A0), w.inst('dsdv2')],
         'syl2anc', '( %s -> X ( CC _D %s ) ( %s + 0 ) )' % (A0, N1, KX))
bg = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, FP)), w.s([], 'simpr', '( %s -> ( X e. dom ( CC _D F ) /\\ X =/= P ) )' % A0), w.inst('dsdv3')],
         'syl2anc', '( %s -> X ( CC _D %s ) %s )' % (A0, G1, LX))
mul = w.s([n1f, d['epc'], g1f, d['epc'], d['ccs'], bf, bg, ek], 'dvmulbr', '( %s -> X ( CC _D ( %s oF x. %s ) ) %s )' % (A0, N1, G1, VAL))
dex = w.s([d['dss'], closed(w, A0, 'cnex', 'CC e. _V')], 'ssexd', '( %s -> D e. _V )' % A0)
epex = w.s([dex, w.inst('difexg')], 'syl', '( %s -> %s e. _V )' % (A0, EP))
off = w.s([epex, nc, rc, w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, N1, N1)), w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, G1, G1))], 'offval2',
          '( %s -> ( %s oF x. %s ) = ( z e. %s |-> ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) ) )' % (A0, N1, G1, EP))
dv = w.s([nc, zpc, zpne], 'divrecd', '( %s -> %s = ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) )' % (A1, QUO('z')))
off2 = w.s([off, w.s([w.s([dv], 'mpteq2dva', '( %s -> %s = ( z e. %s |-> ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) ) )' % (A0, QPF, EP))],
                    'eqcomd', '( %s -> ( z e. %s |-> ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) ) = %s )' % (A0, EP, QPF))], 'eqtrd',
           '( %s -> ( %s oF x. %s ) = %s )' % (A0, N1, G1, QPF))
brq = w.s([mul, w.s([w.s([off2], 'oveq2d', '( %s -> ( CC _D ( %s oF x. %s ) ) = ( CC _D %s ) )' % (A0, N1, G1, QPF))], 'breqd',
                    '( %s -> ( X ( CC _D ( %s oF x. %s ) ) %s <-> X ( CC _D %s ) %s ) )' % (A0, N1, G1, VAL, QPF, VAL))], 'mpbid',
          '( %s -> X ( CC _D %s ) %s )' % (A0, QPF, VAL))
xex = w.s([d['xc']], 'elexd', '( %s -> X e. _V )' % A0)
vex = closed(w, A0, 'ovex', '%s e. _V' % VAL)
w.qed([xex, vex, brq, w.inst('breldmg')], 'syl3anc', '( %s -> X e. dom ( CC _D %s ) )' % (A0, QPF)); run(w)

# ---- dsdv: holomorphy of the extended difference quotient off the base point
w = W('dsdv', 'The extended difference quotient is differentiable wherever the function is, except at the base point.')
FPCC = '( F e. ( D -cn-> CC ) /\\ P e. D /\\ C e. CC )'
DOMP = '( dom ( CC _D F ) \\ { P } )'
A0 = FPCC
A1 = '( %s /\\ g e. %s )' % (A0, DOMP)
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pd = w.s([], 'simp2', '( %s -> P e. D )' % A0)
ccl = w.s([], 'simp3', '( %s -> C e. CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ccs = closed(w, A0, 'ssid', 'CC C_ CC')
epd = closed(w, A0, 'difss', '%s C_ D' % EP)
epc = w.s([epd, dss], 'sstrd', '( %s -> %s C_ CC )' % (A0, EP))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
et = w.s([w.s([], 'cnrestid', '%s = %s' % (JCC, TOP))], 'eqcomi', '%s = %s' % (TOP, JCC))
dsfn = w.s([w.s([fcn, pd, ccl], '3jca', '( %s -> %s )' % (A0, FPCC)), w.inst('dsf')], 'syl', '( %s -> %s : D --> CC )' % (A0, DSF))
res = w.s([w.s([fcn, pd], 'jca', '( %s -> %s )' % (A0, FP)), w.inst('dsres')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, DSF, EP, QPF))
dvr = w.s([w.s([w.s([ccs, dsfn], 'jca', '( %s -> ( CC C_ CC /\\ %s : D --> CC ) )' % (A0, DSF)),
                w.s([dss, epc], 'jca', '( %s -> ( D C_ CC /\\ %s C_ CC ) )' % (A0, EP))], 'jca',
               '( %s -> ( ( CC C_ CC /\\ %s : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) )' % (A0, DSF, EP)),
           w.s([ek, et], 'dvres', '( ( ( CC C_ CC /\\ %s : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (DSF, EP, DSF, EP, DSF, INTEP))],
          'syl', '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (A0, DSF, EP, DSF, INTEP))
qeq = w.s([w.s([w.s([res], 'oveq2d', '( %s -> ( CC _D ( %s |` %s ) ) = ( CC _D %s ) )' % (A0, DSF, EP, QPF))], 'eqcomd',
               '( %s -> ( CC _D %s ) = ( CC _D ( %s |` %s ) ) )' % (A0, QPF, DSF, EP)), dvr], 'eqtrd',
          '( %s -> ( CC _D %s ) = ( ( CC _D %s ) |` %s ) )' % (A0, QPF, DSF, INTEP))
dmq = w.s([w.s([qeq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( ( CC _D %s ) |` %s ) )' % (A0, QPF, DSF, INTEP)),
           closed(w, A0, 'dmres', 'dom ( ( CC _D %s ) |` %s ) = ( %s i^i dom ( CC _D %s ) )' % (DSF, INTEP, INTEP, DSF))], 'eqtrd',
          '( %s -> dom ( CC _D %s ) = ( %s i^i dom ( CC _D %s ) ) )' % (A0, QPF, INTEP, DSF))
dmss = w.s([dmq, closed(w, A0, 'inss2', '( %s i^i dom ( CC _D %s ) ) C_ dom ( CC _D %s )' % (INTEP, DSF, DSF))], 'eqsstrd',
           '( %s -> dom ( CC _D %s ) C_ dom ( CC _D %s ) )' % (A0, QPF, DSF))
gm = w.s([], 'simpr', '( %s -> g e. %s )' % (A1, DOMP))
gdm = w.s([gm, w.inst('eldifi')], 'syl', '( %s -> g e. dom ( CC _D F ) )' % A1)
gne = w.s([w.s([gm, w.inst('eldifsn')], 'sylib', '( %s -> ( g e. dom ( CC _D F ) /\\ g =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> g =/= P )' % A1)
gq = w.s([w.s([w.s([fcn], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % A1), w.s([pd], 'adantr', '( %s -> P e. D )' % A1)], 'jca', '( %s -> %s )' % (A1, FP)),
          w.s([gdm, gne], 'jca', '( %s -> ( g e. dom ( CC _D F ) /\\ g =/= P ) )' % A1), w.inst('dsdv4')], 'syl2anc',
         '( %s -> g e. dom ( CC _D %s ) )' % (A1, QPF))
gd = w.s([w.s([dmss], 'adantr', '( %s -> dom ( CC _D %s ) C_ dom ( CC _D %s ) )' % (A1, QPF, DSF)), gq], 'sseldd',
         '( %s -> g e. dom ( CC _D %s ) )' % (A1, DSF))
w.qed([w.s([gd], 'ex', '( %s -> ( g e. %s -> g e. dom ( CC _D %s ) ) )' % (A0, DOMP, DSF))], 'ssrdv',
      '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, DOMP, DSF)); run(w)
