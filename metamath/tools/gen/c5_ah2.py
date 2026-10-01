"""C5, Abel holomorphy 2: the mean-value bound for the logarithmically weighted
power ( log t ) t^-Z between consecutive integers (C3's cxpmvt template)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

RZ = '( Re ` Z )'
NZ = '-u Z'
ICC = '( K [,] ( K + 1 ) )'
IOO = '( K (,) ( K + 1 ) )'
LG = lambda b: '( log ` %s )' % b
FB = lambda b: '( %s x. ( %s ^c %s ) )' % (LG(b), b, NZ)
DB = lambda b: '( ( ( 1 / %s ) x. ( %s ^c %s ) ) + ( ( %s x. ( %s ^c ( %s - 1 ) ) ) x. %s ) )' % (b, b, NZ, NZ, b, NZ, LG(b))
FRP = '( b e. RR+ |-> %s )' % FB('b')
DRP = '( b e. RR+ |-> %s )' % DB('b')
FIC = '( b e. %s |-> %s )' % (ICC, FB('b'))
DIO = '( b e. %s |-> %s )' % (IOO, DB('b'))
LK1 = LG('( K + 1 )')
MB = '( ( 1 + ( ( abs ` Z ) x. %s ) ) x. ( K ^c ( -u %s - 1 ) ) )' % (LK1, RZ)
JR = '( %s |`t RR )' % TOP

w = W('lgcxpmvt', 'The mean-value bound on the difference of ` ( log t ) t ^c -u Z ` at consecutive '
      'positive integers ( ~ dvlip ; C3\'s ~ cxpmvt with the logarithmic weight ).')
A0 = '( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s )' % RZ
kn = w.s([], 'simpll', '( %s -> K e. NN )' % A0)
zc = w.s([], 'simplr', '( %s -> Z e. CC )' % A0)
rzp = w.s([], 'simpr', '( %s -> 0 < %s )' % (A0, RZ))
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
nzc = w.s([zc], 'negcld', '( %s -> %s e. CC )' % (A0, NZ))
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0)
kpos = w.s([kn], 'nngt0d', '( %s -> 0 < K )' % A0)
k1 = w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)
r1 = a1(w, A0, '1re', '1 e. RR')
onec = a1(w, A0, 'ax-1cn', '1 e. CC')
k1r = w.s([kr, r1], 'readdcld', '( %s -> ( K + 1 ) e. RR )' % A0)
k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
sr = a1(w, A0, 'prid1', 'RR e. { RR , CC }')
absz = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
absz0 = w.s([zc], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % A0)
lk1r = w.s([w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'relogcld', '( %s -> %s e. RR )' % (A0, LK1))
lk10 = w.s([k1r, w.s([r1, k1r, w.s([r1, kr, k1r, k1, w.s([kr], 'ltp1d', '( %s -> K < ( K + 1 ) )' % A0)], 'lelttrd', '( %s -> 1 < ( K + 1 ) )' % A0)], 'ltled',
                    '( %s -> 1 <_ ( K + 1 ) )' % A0), w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (A0, LK1))


# ---- the derivative on the positive reals ---------------------------------
def termcl(w, ante, b, bc, brp, nzcb):
    """closures of the pieces at b: (log b e. CC, b^-Z e. CC, -Z-1 e. CC, b^(-Z-1) e. CC, 1/b e. CC, DB e. CC)"""
    lg = w.s([w.s([brp], 'relogcld', '( %s -> %s e. RR )' % (ante, LG(b)))], 'recnd', '( %s -> %s e. CC )' % (ante, LG(b)))
    pw = w.s([bc, nzcb, w.inst('cxpcl')], 'syl2anc', '( %s -> ( %s ^c %s ) e. CC )' % (ante, b, NZ))
    em1 = w.s([nzcb, a1(w, ante, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (ante, NZ))
    pw1 = w.s([bc, em1, w.inst('cxpcl')], 'syl2anc', '( %s -> ( %s ^c ( %s - 1 ) ) e. CC )' % (ante, b, NZ))
    rb = w.s([w.s([brp], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (ante, b))], 'rpcnd', '( %s -> ( 1 / %s ) e. CC )' % (ante, b))
    t1 = w.s([rb, pw], 'mulcld', '( %s -> ( ( 1 / %s ) x. ( %s ^c %s ) ) e. CC )' % (ante, b, b, NZ))
    t2 = w.s([w.s([nzcb, pw1], 'mulcld', '( %s -> ( %s x. ( %s ^c ( %s - 1 ) ) ) e. CC )' % (ante, NZ, b, NZ)), lg], 'mulcld',
              '( %s -> ( ( %s x. ( %s ^c ( %s - 1 ) ) ) x. %s ) e. CC )' % (ante, NZ, b, NZ, LG(b)))
    return lg, pw, em1, pw1, rb, t1, t2, w.s([t1, t2], 'addcld', '( %s -> %s e. CC )' % (ante, DB(b)))


Arp = '( %s /\\ b e. RR+ )' % A0
brp = w.s([], 'simpr', '( %s -> b e. RR+ )' % Arp)
bc = w.s([brp], 'rpcnd', '( %s -> b e. CC )' % Arp)
nzcr = w.s([nzc], 'adantr', '( %s -> %s e. CC )' % (Arp, NZ))
lg, pw, em1, pw1, rb, t1, t2, dbc = termcl(w, Arp, 'b', bc, brp, nzcr)
fbc = w.s([lg, pw], 'mulcld', '( %s -> %s e. CC )' % (Arp, FB('b')))
# ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) = ( b e. RR+ |-> ( 1 / b ) )
lf = w.s([w.s([], 'relogf1o', '( log |` RR+ ) : RR+ -1-1-onto-> RR'), w.inst('f1of')], 'ax-mp', '( log |` RR+ ) : RR+ --> RR')
lmp = w.s([w.s([lf], 'a1i', '( %s -> ( log |` RR+ ) : RR+ --> RR )' % A0)], 'feqmptd', '( %s -> ( log |` RR+ ) = ( b e. RR+ |-> ( ( log |` RR+ ) ` b ) ) )' % A0)
lmp2 = w.s([lmp, w.s([w.s([brp, w.inst('fvres')], 'syl', '( %s -> ( ( log |` RR+ ) ` b ) = ( log ` b ) )' % Arp)], 'mpteq2dva',
                     '( %s -> ( b e. RR+ |-> ( ( log |` RR+ ) ` b ) ) = ( b e. RR+ |-> ( log ` b ) ) )' % A0)], 'eqtrd',
           '( %s -> ( log |` RR+ ) = ( b e. RR+ |-> ( log ` b ) ) )' % A0)
dlog = w.s([], 'dvrelog', '( RR _D ( log |` RR+ ) ) = ( x e. RR+ |-> ( 1 / x ) )')
cbv = w.s([w.s([], 'oveq2', '( x = b -> ( 1 / x ) = ( 1 / b ) )')], 'cbvmptv', '( x e. RR+ |-> ( 1 / x ) ) = ( b e. RR+ |-> ( 1 / b ) )')
dlog2 = w.s([w.s([w.s([dlog, cbv], 'eqtri', '( RR _D ( log |` RR+ ) ) = ( b e. RR+ |-> ( 1 / b ) )')], 'a1i', '( %s -> ( RR _D ( log |` RR+ ) ) = ( b e. RR+ |-> ( 1 / b ) ) )' % A0)],
           'idi', '( %s -> ( RR _D ( log |` RR+ ) ) = ( b e. RR+ |-> ( 1 / b ) ) )' % A0)
dlg = w.s([w.s([w.s([lmp2], 'oveq2d', '( %s -> ( RR _D ( log |` RR+ ) ) = ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) )' % A0)], 'eqcomd',
               '( %s -> ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) = ( RR _D ( log |` RR+ ) ) )' % A0), dlog2], 'eqtrd',
          '( %s -> ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) = ( b e. RR+ |-> ( 1 / b ) ) )' % A0)
dcx = w.s([nzc, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( b e. RR+ |-> ( b ^c %s ) ) ) = ( b e. RR+ |-> ( %s x. ( b ^c ( %s - 1 ) ) ) ) )' % (A0, NZ, NZ, NZ))
d1 = w.s([w.s([nzcr, pw1], 'mulcld', '( %s -> ( %s x. ( b ^c ( %s - 1 ) ) ) e. CC )' % (Arp, NZ, NZ))], 'idi', '( %s -> ( %s x. ( b ^c ( %s - 1 ) ) ) e. CC )' % (Arp, NZ, NZ))
dv1 = w.s([sr, lg, rb, dlg, pw, d1, dcx], 'dvmptmul', '( %s -> ( RR _D %s ) = %s )' % (A0, FRP, DRP))
# continuity on RR+ and restriction to the closed interval (cxpmvt's route)
ffrp = w.s([fbc, w.s([], 'eqid', '%s = %s' % (FRP, FRP))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, FRP))
fdrp = w.s([dbc, w.s([], 'eqid', '%s = %s' % (DRP, DRP))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, DRP))
dmd = w.s([w.s([dv1], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom %s )' % (A0, FRP, DRP)), w.s([fdrp, w.inst('fdm')], 'syl', '( %s -> dom %s = RR+ )' % (A0, DRP))], 'eqtrd',
          '( %s -> dom ( RR _D %s ) = RR+ )' % (A0, FRP))
rrcc = a1(w, A0, 'ax-resscn', 'RR C_ CC')
rpre = a1(w, A0, 'rpssre', 'RR+ C_ RR')
cnrp = w.s([w.s([w.s([rrcc, ffrp, rpre], '3jca', '( %s -> ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) )' % (A0, FRP)), dmd], 'jca',
                '( %s -> ( ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) /\\ dom ( RR _D %s ) = RR+ ) )' % (A0, FRP, FRP)), w.inst('dvcn')], 'syl',
           '( %s -> %s e. ( RR+ -cn-> CC ) )' % (A0, FRP))
Aic = '( %s /\\ b e. %s )' % (A0, ICC)
bic = w.s([], 'simpr', '( %s -> b e. %s )' % (Aic, ICC))
icre = w.s([kr, k1r, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, ICC))
bre = w.s([w.s([icre], 'adantr', '( %s -> %s C_ RR )' % (Aic, ICC)), bic], 'sseldd', '( %s -> b e. RR )' % Aic)
icbi = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( b e. %s <-> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) ) )' % (A0, ICC))
icp = w.s([bic, w.s([icbi], 'adantr', '( %s -> ( b e. %s <-> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) ) )' % (Aic, ICC))], 'mpbid',
          '( %s -> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) )' % Aic)
kleb = w.s([icp, w.inst('simp2')], 'syl', '( %s -> K <_ b )' % Aic)
bpos = w.s([a1(w, Aic, '0re', '0 e. RR'), w.s([kr], 'adantr', '( %s -> K e. RR )' % Aic), bre, w.s([kpos], 'adantr', '( %s -> 0 < K )' % Aic), kleb], 'ltletrd',
           '( %s -> 0 < b )' % Aic)
icrp = w.s([bre, bpos], 'elrpd', '( %s -> b e. RR+ )' % Aic)
icssrp = w.s([w.s([icrp], 'ex', '( %s -> ( b e. %s -> b e. RR+ ) )' % (A0, ICC))], 'ssrdv', '( %s -> %s C_ RR+ )' % (A0, ICC))
resc = w.s([cnrp, w.s([icssrp, w.inst('rescncf')], 'syl', '( %s -> ( %s e. ( RR+ -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, FRP, FRP, ICC, ICC))], 'mpd',
           '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0, FRP, ICC, ICC))
rsm = w.s([icssrp, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, FRP, ICC, FIC))
hF = w.s([w.s([rsm], 'eqcomd', '( %s -> %s = ( %s |` %s ) )' % (A0, FIC, FRP, ICC)), resc], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, FIC, ICC))
ejr = w.s([], 'eqid', '%s = %s' % (JR, JR))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
tg = w.s([], 'tgioo4', '%s = %s' % (RETOP, JR))
ntr0 = w.s([kr, k1r, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, RETOP, ICC, IOO))
jeq = w.s([w.s([tg], 'eqcomi', '%s = %s' % (JR, RETOP))], 'a1i', '( %s -> %s = %s )' % (A0, JR, RETOP))
ntr = w.s([w.s([w.s([jeq], 'fveq2d', '( %s -> ( int ` %s ) = ( int ` %s ) )' % (A0, JR, RETOP))], 'fveq1d', '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` %s ) ` %s ) )' % (A0, JR, ICC, RETOP, ICC)), ntr0],
          'eqtrd', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, JR, ICC, IOO))
dvic = w.s([sr, fbc, dbc, dv1, icssrp, ejr, ek, ntr], 'dvmptres2', '( %s -> ( RR _D %s ) = %s )' % (A0, FIC, DIO))
Aio = '( %s /\\ b e. %s )' % (A0, IOO)
bio = w.s([], 'simpr', '( %s -> b e. %s )' % (Aio, IOO))
iossic = a1(w, A0, 'ioossicc', '%s C_ %s' % (IOO, ICC))
iossrp = w.s([iossic, icssrp], 'sstrd', '( %s -> %s C_ RR+ )' % (A0, IOO))
biorp = w.s([w.s([iossrp], 'adantr', '( %s -> %s C_ RR+ )' % (Aio, IOO)), bio], 'sseldd', '( %s -> b e. RR+ )' % Aio)
dbio = termcl(w, Aio, 'b', w.s([biorp], 'rpcnd', '( %s -> b e. CC )' % Aio), biorp, w.s([nzc], 'adantr', '( %s -> %s e. CC )' % (Aio, NZ)))[7]
fdio = w.s([dbio, w.s([], 'eqid', '%s = %s' % (DIO, DIO))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, DIO, IOO))
hD = w.s([w.s([dvic], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom %s )' % (A0, FIC, DIO)), w.s([fdio, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A0, DIO, IOO))], 'eqtrd',
         '( %s -> dom ( RR _D %s ) = %s )' % (A0, FIC, IOO))
# ---- the bound on the derivative over the open interval ---------------------
IOX = '( %s /\\ x e. %s )' % (A0, IOO)
xio = w.s([], 'simpr', '( %s -> x e. %s )' % (IOX, IOO))
xrp = w.s([w.s([iossrp], 'adantr', '( %s -> %s C_ RR+ )' % (IOX, IOO)), xio], 'sseldd', '( %s -> x e. RR+ )' % IOX)
xcc = w.s([xrp], 'rpcnd', '( %s -> x e. CC )' % IOX)
xr = w.s([xrp], 'rpred', '( %s -> x e. RR )' % IOX)
nzx = w.s([nzc], 'adantr', '( %s -> %s e. CC )' % (IOX, NZ))
zcx = w.s([zc], 'adantr', '( %s -> Z e. CC )' % IOX)
lgx, pwx, em1x, pw1x, rbx, t1x, t2x, dbx = termcl(w, IOX, 'x', xcc, xrp, nzx)
subx = w.s([w.s([w.s([], 'oveq2', '( b = x -> ( 1 / b ) = ( 1 / x ) )'), w.s([], 'oveq1', '( b = x -> ( b ^c %s ) = ( x ^c %s ) )' % (NZ, NZ))], 'oveq12d',
                '( b = x -> ( ( 1 / b ) x. ( b ^c %s ) ) = ( ( 1 / x ) x. ( x ^c %s ) ) )' % (NZ, NZ)),
            w.s([w.s([w.s([], 'oveq1', '( b = x -> ( b ^c ( %s - 1 ) ) = ( x ^c ( %s - 1 ) ) )' % (NZ, NZ))], 'oveq2d',
                     '( b = x -> ( %s x. ( b ^c ( %s - 1 ) ) ) = ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (NZ, NZ, NZ, NZ)), w.s([], 'fveq2', '( b = x -> ( log ` b ) = ( log ` x ) )')], 'oveq12d',
                '( b = x -> ( ( %s x. ( b ^c ( %s - 1 ) ) ) x. ( log ` b ) ) = ( ( %s x. ( x ^c ( %s - 1 ) ) ) x. ( log ` x ) ) )' % (NZ, NZ, NZ, NZ))], 'oveq12d',
           '( b = x -> %s = %s )' % (DB('b'), DB('x')))
vx = mpv(w, IOX, DIO, 'x', DB('x'), subx, xio, vexd(w, IOX, DB('x')), IOO)
dvx2 = w.s([w.s([w.s([dvic], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (IOX, FIC, DIO))], 'fveq1d', '( %s -> ( ( RR _D %s ) ` x ) = ( %s ` x ) )' % (IOX, FIC, DIO)), vx], 'eqtrd',
           '( %s -> ( ( RR _D %s ) ` x ) = %s )' % (IOX, FIC, DB('x')))
# the modulus of each piece
rzx = w.s([rz], 'adantr', '( %s -> %s e. RR )' % (IOX, RZ))
onex = a1(w, IOX, 'ax-1cn', '1 e. CC')
rex = w.s([w.s([nzx, onex, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( %s - 1 ) ) = ( ( Re ` %s ) - ( Re ` 1 ) ) )' % (IOX, NZ, NZ)),
           w.s([w.s([zcx, w.inst('reneg')], 'syl', '( %s -> ( Re ` %s ) = -u %s )' % (IOX, NZ, RZ)), a1(w, IOX, 're1', '( Re ` 1 ) = 1')], 'oveq12d',
               '( %s -> ( ( Re ` %s ) - ( Re ` 1 ) ) = ( -u %s - 1 ) )' % (IOX, NZ, RZ))], 'eqtrd', '( %s -> ( Re ` ( %s - 1 ) ) = ( -u %s - 1 ) )' % (IOX, NZ, RZ))
XP = '( x ^c ( -u %s - 1 ) )' % RZ
KP = '( K ^c ( -u %s - 1 ) )' % RZ
abp1 = w.s([w.s([xrp, em1x, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` ( x ^c ( %s - 1 ) ) ) = ( x ^c ( Re ` ( %s - 1 ) ) ) )' % (IOX, NZ, NZ)),
            w.s([rex], 'oveq2d', '( %s -> ( x ^c ( Re ` ( %s - 1 ) ) ) = %s )' % (IOX, NZ, XP))], 'eqtrd', '( %s -> ( abs ` ( x ^c ( %s - 1 ) ) ) = %s )' % (IOX, NZ, XP))
# first piece: ( 1 / x ) x. ( x ^c -u Z ), modulus = x ^c ( -u sigma - 1 )
abpw = w.s([w.s([xrp, nzx, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` ( x ^c %s ) ) = ( x ^c ( Re ` %s ) ) )' % (IOX, NZ, NZ)),
            w.s([w.s([zcx, w.inst('reneg')], 'syl', '( %s -> ( Re ` %s ) = -u %s )' % (IOX, NZ, RZ))], 'oveq2d', '( %s -> ( x ^c ( Re ` %s ) ) = ( x ^c -u %s ) )' % (IOX, NZ, RZ))],
           'eqtrd', '( %s -> ( abs ` ( x ^c %s ) ) = ( x ^c -u %s ) )' % (IOX, NZ, RZ))
rxrp = w.s([xrp], 'rpreccld', '( %s -> ( 1 / x ) e. RR+ )' % IOX)
abrx = w.s([w.s([rxrp], 'rpred', '( %s -> ( 1 / x ) e. RR )' % IOX), w.s([rxrp], 'rpge0d', '( %s -> 0 <_ ( 1 / x ) )' % IOX)], 'absidd', '( %s -> ( abs ` ( 1 / x ) ) = ( 1 / x ) )' % IOX)
ab1 = w.s([w.s([rbx, pwx], 'absmuld', '( %s -> ( abs ` ( ( 1 / x ) x. ( x ^c %s ) ) ) = ( ( abs ` ( 1 / x ) ) x. ( abs ` ( x ^c %s ) ) ) )' % (IOX, NZ, NZ)),
           w.s([abrx, abpw], 'oveq12d', '( %s -> ( ( abs ` ( 1 / x ) ) x. ( abs ` ( x ^c %s ) ) ) = ( ( 1 / x ) x. ( x ^c -u %s ) ) )' % (IOX, NZ, RZ))], 'eqtrd',
          '( %s -> ( abs ` ( ( 1 / x ) x. ( x ^c %s ) ) ) = ( ( 1 / x ) x. ( x ^c -u %s ) ) )' % (IOX, NZ, RZ))
xne = w.s([xrp], 'rpne0d', '( %s -> x =/= 0 )' % IOX)
xm1 = w.s([w.s([xcc, xne, onex, w.inst('cxpneg')], 'syl3anc', '( %s -> ( x ^c -u 1 ) = ( 1 / ( x ^c 1 ) ) )' % IOX),
           w.s([w.s([xcc, w.inst('cxp1')], 'syl', '( %s -> ( x ^c 1 ) = x )' % IOX)], 'oveq2d', '( %s -> ( 1 / ( x ^c 1 ) ) = ( 1 / x ) )' % IOX)], 'eqtrd',
          '( %s -> ( x ^c -u 1 ) = ( 1 / x ) )' % IOX)
nrzc = w.s([w.s([rzx], 'renegcld', '( %s -> -u %s e. RR )' % (IOX, RZ))], 'recnd', '( %s -> -u %s e. CC )' % (IOX, RZ))
m1c = a1(w, IOX, 'neg1cn', '-u 1 e. CC')
cadd = w.s([w.s([xcc, xne], 'jca', '( %s -> ( x e. CC /\\ x =/= 0 ) )' % IOX), m1c, nrzc, w.inst('cxpadd')], 'syl3anc',
           '( %s -> ( x ^c ( -u 1 + -u %s ) ) = ( ( x ^c -u 1 ) x. ( x ^c -u %s ) ) )' % (IOX, RZ, RZ))
ee = w.s([w.s([m1c, nrzc], 'addcomd', '( %s -> ( -u 1 + -u %s ) = ( -u %s + -u 1 ) )' % (IOX, RZ, RZ)), w.s([nrzc, onex], 'negsubd', '( %s -> ( -u %s + -u 1 ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))],
         'eqtrd', '( %s -> ( -u 1 + -u %s ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))
p1eq0 = w.s([cadd, w.s([xm1], 'oveq1d', '( %s -> ( ( x ^c -u 1 ) x. ( x ^c -u %s ) ) = ( ( 1 / x ) x. ( x ^c -u %s ) ) )' % (IOX, RZ, RZ))], 'eqtrd',
            '( %s -> ( x ^c ( -u 1 + -u %s ) ) = ( ( 1 / x ) x. ( x ^c -u %s ) ) )' % (IOX, RZ, RZ))
p1eq = w.s([w.s([ee], 'oveq2d', '( %s -> ( x ^c ( -u 1 + -u %s ) ) = %s )' % (IOX, RZ, XP)), p1eq0], 'eqtr3d', '( %s -> %s = ( ( 1 / x ) x. ( x ^c -u %s ) ) )' % (IOX, XP, RZ))
ab1e = w.s([ab1, w.s([p1eq], 'eqcomd', '( %s -> ( ( 1 / x ) x. ( x ^c -u %s ) ) = %s )' % (IOX, RZ, XP))], 'eqtrd', '( %s -> ( abs ` ( ( 1 / x ) x. ( x ^c %s ) ) ) = %s )' % (IOX, NZ, XP))
# second piece: ( -u Z x. x ^c ( -u Z - 1 ) ) x. log x, modulus = ( |Z| x. XP ) x. log x
lgxr = w.s([xrp], 'relogcld', '( %s -> ( log ` x ) e. RR )' % IOX)
kx = w.s([w.s([xio, w.inst('eliooord')], 'syl', '( %s -> ( K < x /\\ x < ( K + 1 ) ) )' % IOX), w.inst('simpl')], 'syl', '( %s -> K < x )' % IOX)
xk1 = w.s([w.s([xio, w.inst('eliooord')], 'syl', '( %s -> ( K < x /\\ x < ( K + 1 ) ) )' % IOX), w.inst('simpr')], 'syl', '( %s -> x < ( K + 1 ) )' % IOX)
klex = w.s([w.s([kr], 'adantr', '( %s -> K e. RR )' % IOX), xr, kx], 'ltled', '( %s -> K <_ x )' % IOX)
x1 = w.s([a1(w, IOX, '1re', '1 e. RR'), w.s([kr], 'adantr', '( %s -> K e. RR )' % IOX), xr, w.s([k1], 'adantr', '( %s -> 1 <_ K )' % IOX), klex], 'letrd', '( %s -> 1 <_ x )' % IOX)
lgx0 = w.s([xr, x1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` x ) )' % IOX)
ablg = w.s([lgxr, lgx0], 'absidd', '( %s -> ( abs ` ( log ` x ) ) = ( log ` x ) )' % IOX)
abnz = w.s([zcx], 'absnegd', '( %s -> ( abs ` %s ) = ( abs ` Z ) )' % (IOX, NZ))
ab2a = w.s([w.s([nzx, pw1x], 'absmuld', '( %s -> ( abs ` ( %s x. ( x ^c ( %s - 1 ) ) ) ) = ( ( abs ` %s ) x. ( abs ` ( x ^c ( %s - 1 ) ) ) ) )' % (IOX, NZ, NZ, NZ, NZ)),
           w.s([abnz, abp1], 'oveq12d', '( %s -> ( ( abs ` %s ) x. ( abs ` ( x ^c ( %s - 1 ) ) ) ) = ( ( abs ` Z ) x. %s ) )' % (IOX, NZ, NZ, XP))], 'eqtrd',
          '( %s -> ( abs ` ( %s x. ( x ^c ( %s - 1 ) ) ) ) = ( ( abs ` Z ) x. %s ) )' % (IOX, NZ, NZ, XP))
ZX1 = '( %s x. ( x ^c ( %s - 1 ) ) )' % (NZ, NZ)
zx1c = w.s([nzx, pw1x], 'mulcld', '( %s -> %s e. CC )' % (IOX, ZX1))
ab2 = w.s([w.s([zx1c, lgx], 'absmuld', '( %s -> ( abs ` ( %s x. ( log ` x ) ) ) = ( ( abs ` %s ) x. ( abs ` ( log ` x ) ) ) )' % (IOX, ZX1, ZX1)),
           w.s([ab2a, ablg], 'oveq12d', '( %s -> ( ( abs ` %s ) x. ( abs ` ( log ` x ) ) ) = ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) )' % (IOX, ZX1, XP))], 'eqtrd',
          '( %s -> ( abs ` ( %s x. ( log ` x ) ) ) = ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) )' % (IOX, ZX1, XP))
# the antitone bound XP <_ KP and log x <_ log ( K + 1 )
rz1 = w.s([rzx, a1(w, IOX, '1re', '1 e. RR')], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (IOX, RZ))
rz10 = w.s([a1(w, IOX, '0re', '0 e. RR'), rz1, w.s([a1(w, IOX, '0re', '0 e. RR'), rzx, rz1, w.s([rzp], 'adantr', '( %s -> 0 < %s )' % (IOX, RZ)), w.s([rzx], 'ltp1d', '( %s -> %s < ( %s + 1 ) )' % (IOX, RZ, RZ))],
                                                        'lttrd', '( %s -> 0 < ( %s + 1 ) )' % (IOX, RZ))], 'ltled', '( %s -> 0 <_ ( %s + 1 ) )' % (IOX, RZ))
negd = w.s([w.s([w.s([rzx], 'recnd', '( %s -> %s e. CC )' % (IOX, RZ)), onex], 'negdid', '( %s -> -u ( %s + 1 ) = ( -u %s + -u 1 ) )' % (IOX, RZ, RZ)),
            w.s([nrzc, onex], 'negsubd', '( %s -> ( -u %s + -u 1 ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))], 'eqtrd', '( %s -> -u ( %s + 1 ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))
anti = w.s([w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % IOX), xrp, rz1], '3jca', '( %s -> ( K e. RR+ /\\ x e. RR+ /\\ ( %s + 1 ) e. RR ) )' % (IOX, RZ)),
                 w.s([rz10, klex], 'jca', '( %s -> ( 0 <_ ( %s + 1 ) /\\ K <_ x ) )' % (IOX, RZ))], 'jca',
                '( %s -> ( ( K e. RR+ /\\ x e. RR+ /\\ ( %s + 1 ) e. RR ) /\\ ( 0 <_ ( %s + 1 ) /\\ K <_ x ) ) )' % (IOX, RZ, RZ)), w.inst('cxpnegle')], 'syl',
           '( %s -> ( x ^c -u ( %s + 1 ) ) <_ ( K ^c -u ( %s + 1 ) ) )' % (IOX, RZ, RZ))
anti3 = w.s([w.s([w.s([w.s([negd], 'oveq2d', '( %s -> ( x ^c -u ( %s + 1 ) ) = %s )' % (IOX, RZ, XP))], 'eqcomd', '( %s -> %s = ( x ^c -u ( %s + 1 ) ) )' % (IOX, XP, RZ)), anti], 'eqbrtrd',
                 '( %s -> %s <_ ( K ^c -u ( %s + 1 ) ) )' % (IOX, XP, RZ)), w.s([negd], 'oveq2d', '( %s -> ( K ^c -u ( %s + 1 ) ) = %s )' % (IOX, RZ, KP))], 'breqtrd',
            '( %s -> %s <_ %s )' % (IOX, XP, KP))
nrz1 = w.s([rz1], 'renegcld', '( %s -> -u ( %s + 1 ) e. RR )' % (IOX, RZ))
xpr = w.s([w.s([w.s([xrp, nrz1], 'rpcxpcld', '( %s -> ( x ^c -u ( %s + 1 ) ) e. RR+ )' % (IOX, RZ))], 'rpred', '( %s -> ( x ^c -u ( %s + 1 ) ) e. RR )' % (IOX, RZ)),
            w.s([negd], 'oveq2d', '( %s -> ( x ^c -u ( %s + 1 ) ) = %s )' % (IOX, RZ, XP))], 'eqeltrrd', '( %s -> %s e. RR )' % (IOX, XP))
xp0 = w.s([w.s([w.s([w.s([xrp, nrz1], 'rpcxpcld', '( %s -> ( x ^c -u ( %s + 1 ) ) e. RR+ )' % (IOX, RZ))], 'rpge0d', '( %s -> 0 <_ ( x ^c -u ( %s + 1 ) ) )' % (IOX, RZ)),
                w.s([negd], 'oveq2d', '( %s -> ( x ^c -u ( %s + 1 ) ) = %s )' % (IOX, RZ, XP))], 'breqtrd', '( %s -> 0 <_ %s )' % (IOX, XP))], 'idi', '( %s -> 0 <_ %s )' % (IOX, XP))
kpr = w.s([w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % IOX), nrz1], 'rpcxpcld', '( %s -> ( K ^c -u ( %s + 1 ) ) e. RR+ )' % (IOX, RZ))], 'rpred',
                '( %s -> ( K ^c -u ( %s + 1 ) ) e. RR )' % (IOX, RZ)), w.s([negd], 'oveq2d', '( %s -> ( K ^c -u ( %s + 1 ) ) = %s )' % (IOX, RZ, KP))], 'eqeltrrd', '( %s -> %s e. RR )' % (IOX, KP))
lgle = w.s([w.s([w.s([xr], 'idi', '( %s -> x e. RR )' % IOX), w.s([k1r], 'adantr', '( %s -> ( K + 1 ) e. RR )' % IOX), xk1], 'ltled', '( %s -> x <_ ( K + 1 ) )' % IOX),
            w.s([xrp, w.s([w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'adantr', '( %s -> ( K + 1 ) e. RR+ )' % IOX), w.inst('logleb')], 'syl2anc',
                '( %s -> ( x <_ ( K + 1 ) <-> ( log ` x ) <_ %s ) )' % (IOX, LK1))], 'mpbid', '( %s -> ( log ` x ) <_ %s )' % (IOX, LK1))
abszx = w.s([absz], 'adantr', '( %s -> ( abs ` Z ) e. RR )' % IOX)
absz0x = w.s([absz0], 'adantr', '( %s -> 0 <_ ( abs ` Z ) )' % IOX)
zxp = w.s([abszx, xpr], 'remulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. RR )' % (IOX, XP))
zkp = w.s([abszx, kpr], 'remulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. RR )' % (IOX, KP))
le2a = w.s([w.s([w.s([xpr, kpr, w.s([abszx, absz0x], 'jca', '( %s -> ( ( abs ` Z ) e. RR /\\ 0 <_ ( abs ` Z ) ) )' % IOX)], '3jca',
                     '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( ( abs ` Z ) e. RR /\\ 0 <_ ( abs ` Z ) ) ) )' % (IOX, XP, KP)), anti3, w.inst('lemul2a')], 'syl2anc',
                '( %s -> ( ( abs ` Z ) x. %s ) <_ ( ( abs ` Z ) x. %s ) )' % (IOX, XP, KP))], 'idi', '( %s -> ( ( abs ` Z ) x. %s ) <_ ( ( abs ` Z ) x. %s ) )' % (IOX, XP, KP))
lk1x = w.s([lk1r], 'adantr', '( %s -> %s e. RR )' % (IOX, LK1))
le2 = w.s([zxp, zkp, lgxr, lk1x, w.s([abszx, xpr, absz0x, xp0], 'mulge0d', '( %s -> 0 <_ ( ( abs ` Z ) x. %s ) )' % (IOX, XP)), lgx0, le2a, lgle], 'lemul12ad',
          '( %s -> ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) <_ ( ( ( abs ` Z ) x. %s ) x. %s ) )' % (IOX, XP, KP, LK1))
# assemble: abs DB <_ XP + ( |Z| XP ) log x <_ KP + ( |Z| KP ) log(K+1) = MB
tri = w.s([t1x, t2x, w.inst('abstri')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` ( ( 1 / x ) x. ( x ^c %s ) ) ) + ( abs ` ( %s x. ( log ` x ) ) ) ) )' % (IOX, DB('x'), NZ, ZX1))
tri2 = w.s([tri, w.s([ab1e, ab2], 'oveq12d', '( %s -> ( ( abs ` ( ( 1 / x ) x. ( x ^c %s ) ) ) + ( abs ` ( %s x. ( log ` x ) ) ) ) = ( %s + ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) ) )' % (IOX, NZ, ZX1, XP, XP))],
           'breqtrd', '( %s -> ( abs ` %s ) <_ ( %s + ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) ) )' % (IOX, DB('x'), XP, XP))
zxl = w.s([zxp, lgxr], 'remulcld', '( %s -> ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) e. RR )' % (IOX, XP))
zkl = w.s([zkp, lk1x], 'remulcld', '( %s -> ( ( ( abs ` Z ) x. %s ) x. %s ) e. RR )' % (IOX, KP, LK1))
sm = w.s([xpr, zxl, kpr, zkl, anti3, le2], 'le2addd', '( %s -> ( %s + ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) ) <_ ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) )' % (IOX, XP, XP, KP, KP, LK1))
kpc = w.s([kpr], 'recnd', '( %s -> %s e. CC )' % (IOX, KP))
alg = w.s([w.s([w.s([abszx], 'recnd', '( %s -> ( abs ` Z ) e. CC )' % IOX), kpc, w.s([lk1x], 'recnd', '( %s -> %s e. CC )' % (IOX, LK1))], 'mul32d',
               '( %s -> ( ( ( abs ` Z ) x. %s ) x. %s ) = ( ( ( abs ` Z ) x. %s ) x. %s ) )' % (IOX, KP, LK1, LK1, KP))], 'oveq2d',
          '( %s -> ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) = ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) )' % (IOX, KP, KP, LK1, KP, LK1, KP))
zlc = w.s([w.s([abszx], 'recnd', '( %s -> ( abs ` Z ) e. CC )' % IOX), w.s([lk1x], 'recnd', '( %s -> %s e. CC )' % (IOX, LK1))], 'mulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. CC )' % (IOX, LK1))
dist = w.s([w.s([onex, zlc, kpc], 'adddird', '( %s -> ( ( 1 + ( ( abs ` Z ) x. %s ) ) x. %s ) = ( ( 1 x. %s ) + ( ( ( abs ` Z ) x. %s ) x. %s ) ) )' % (IOX, LK1, KP, KP, LK1, KP)),
            w.s([w.s([kpc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (IOX, KP, KP))], 'oveq1d', '( %s -> ( ( 1 x. %s ) + ( ( ( abs ` Z ) x. %s ) x. %s ) ) = ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) )' % (IOX, KP, LK1, KP, KP, LK1, KP))],
           'eqtrd', '( %s -> %s = ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) )' % (IOX, MB, KP, LK1, KP))
rhs = w.s([alg, w.s([dist], 'eqcomd', '( %s -> ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) = %s )' % (IOX, KP, LK1, KP, MB))], 'eqtrd', '( %s -> ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) = %s )' % (IOX, KP, KP, LK1, MB))
dbr = w.s([dbx], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (IOX, DB('x')))
s1r = w.s([xpr, zxl], 'readdcld', '( %s -> ( %s + ( ( ( abs ` Z ) x. %s ) x. ( log ` x ) ) ) e. RR )' % (IOX, XP, XP))
s2r = w.s([kpr, zkl], 'readdcld', '( %s -> ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) e. RR )' % (IOX, KP, KP, LK1))
hL0 = w.s([dbr, s1r, s2r, tri2, sm], 'letrd', '( %s -> ( abs ` %s ) <_ ( %s + ( ( ( abs ` Z ) x. %s ) x. %s ) ) )' % (IOX, DB('x'), KP, KP, LK1))
hL = w.s([w.s([dvx2], 'fveq2d', '( %s -> ( abs ` ( ( RR _D %s ) ` x ) ) = ( abs ` %s ) )' % (IOX, FIC, DB('x'))), w.s([hL0, rhs], 'breqtrd', '( %s -> ( abs ` %s ) <_ %s )' % (IOX, DB('x'), MB))],
         'eqbrtrd', '( %s -> ( abs ` ( ( RR _D %s ) ` x ) ) <_ %s )' % (IOX, FIC, MB))
nrzr = w.s([rz], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))
hM = w.s([w.s([r1, w.s([absz, lk1r], 'remulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. RR )' % (A0, LK1))], 'readdcld', '( %s -> ( 1 + ( ( abs ` Z ) x. %s ) ) e. RR )' % (A0, LK1)),
          w.s([w.s([krp, w.s([nrzr, r1], 'resubcld', '( %s -> ( -u %s - 1 ) e. RR )' % (A0, RZ))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, KP))], 'rpred', '( %s -> %s e. RR )' % (A0, KP))],
         'remulcld', '( %s -> %s e. RR )' % (A0, MB))
# ---- the Lipschitz bound at the endpoints ----------------------------------
kic = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( K e. %s <-> ( K e. RR /\\ K <_ K /\\ K <_ ( K + 1 ) ) ) )' % (A0, ICC))
kle1 = w.s([kr, k1r, w.s([kr], 'ltp1d', '( %s -> K < ( K + 1 ) )' % A0)], 'ltled', '( %s -> K <_ ( K + 1 ) )' % A0)
kmem = w.s([w.s([kr, w.s([kr], 'leidd', '( %s -> K <_ K )' % A0), kle1], '3jca', '( %s -> ( K e. RR /\\ K <_ K /\\ K <_ ( K + 1 ) ) )' % A0), kic], 'mpbird', '( %s -> K e. %s )' % (A0, ICC))
k1ic = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( K + 1 ) e. %s <-> ( ( K + 1 ) e. RR /\\ K <_ ( K + 1 ) /\\ ( K + 1 ) <_ ( K + 1 ) ) ) )' % (A0, ICC))
k1mem = w.s([w.s([k1r, kle1, w.s([k1r], 'leidd', '( %s -> ( K + 1 ) <_ ( K + 1 ) )' % A0)], '3jca', '( %s -> ( ( K + 1 ) e. RR /\\ K <_ ( K + 1 ) /\\ ( K + 1 ) <_ ( K + 1 ) ) )' % A0), k1ic],
            'mpbird', '( %s -> ( K + 1 ) e. %s )' % (A0, ICC))
lip = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([kmem, k1mem], 'jca', '( %s -> ( K e. %s /\\ ( K + 1 ) e. %s ) )' % (A0, ICC, ICC))], 'jca',
          '( %s -> ( %s /\\ ( K e. %s /\\ ( K + 1 ) e. %s ) ) )' % (A0, A0, ICC, ICC))
dvl = w.s([kr, k1r, hF, hD, hM, hL], 'dvlip', '( ( %s /\\ ( K e. %s /\\ ( K + 1 ) e. %s ) ) -> ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) <_ ( %s x. ( abs ` ( K - ( K + 1 ) ) ) ) )' % (A0, ICC, ICC, FIC, FIC, MB))
dvl2 = w.s([lip, dvl], 'syl', '( %s -> ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) <_ ( %s x. ( abs ` ( K - ( K + 1 ) ) ) ) )' % (A0, FIC, FIC, MB))
subk = w.s([w.s([], 'fveq2', '( b = K -> ( log ` b ) = ( log ` K ) )'), w.s([], 'oveq1', '( b = K -> ( b ^c %s ) = ( K ^c %s ) )' % (NZ, NZ))], 'oveq12d', '( b = K -> %s = %s )' % (FB('b'), FB('K')))
vK = mpv(w, A0, FIC, 'K', FB('K'), subk, kmem, vexd(w, A0, FB('K')), ICC)
subk1 = w.s([w.s([], 'fveq2', '( b = ( K + 1 ) -> ( log ` b ) = ( log ` ( K + 1 ) ) )'), w.s([], 'oveq1', '( b = ( K + 1 ) -> ( b ^c %s ) = ( ( K + 1 ) ^c %s ) )' % (NZ, NZ))], 'oveq12d',
            '( b = ( K + 1 ) -> %s = %s )' % (FB('b'), FB('( K + 1 )')))
vK1 = mpv(w, A0, FIC, '( K + 1 )', FB('( K + 1 )'), subk1, k1mem, vexd(w, A0, FB('( K + 1 )')), ICC)
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
gap = w.s([w.s([kc, w.s([k1r], 'recnd', '( %s -> ( K + 1 ) e. CC )' % A0)], 'abssubd', '( %s -> ( abs ` ( K - ( K + 1 ) ) ) = ( abs ` ( ( K + 1 ) - K ) ) )' % A0),
           w.s([w.s([w.s([kc, onec], 'pncan2d', '( %s -> ( ( K + 1 ) - K ) = 1 )' % A0)], 'fveq2d', '( %s -> ( abs ` ( ( K + 1 ) - K ) ) = ( abs ` 1 ) )' % A0), a1(w, A0, 'abs1', '( abs ` 1 ) = 1')],
               'eqtrd', '( %s -> ( abs ` ( ( K + 1 ) - K ) ) = 1 )' % A0)], 'eqtrd', '( %s -> ( abs ` ( K - ( K + 1 ) ) ) = 1 )' % A0)
rhs2 = w.s([w.s([gap], 'oveq2d', '( %s -> ( %s x. ( abs ` ( K - ( K + 1 ) ) ) ) = ( %s x. 1 ) )' % (A0, MB, MB)), w.s([w.s([hM], 'recnd', '( %s -> %s e. CC )' % (A0, MB))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A0, MB, MB))],
           'eqtrd', '( %s -> ( %s x. ( abs ` ( K - ( K + 1 ) ) ) ) = %s )' % (A0, MB, MB))
lhs = w.s([w.s([vK, vK1], 'oveq12d', '( %s -> ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) = ( %s - %s ) )' % (A0, FIC, FIC, FB('K'), FB('( K + 1 )')))], 'fveq2d',
          '( %s -> ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) = ( abs ` ( %s - %s ) ) )' % (A0, FIC, FIC, FB('K'), FB('( K + 1 )')))
w.qed([w.s([lhs], 'eqcomd', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) )' % (A0, FB('K'), FB('( K + 1 )'), FIC, FIC)),
       w.s([dvl2, rhs2], 'breqtrd', '( %s -> ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) <_ %s )' % (A0, FIC, FIC, MB))], 'eqbrtrd',
      '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A0, FB('K'), FB('( K + 1 )'), MB))
run5(w)
