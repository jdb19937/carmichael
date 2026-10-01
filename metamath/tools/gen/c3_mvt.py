"""Sortie C3 section 8: the mean-value bound on a difference of powers."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

RZ = '( Re ` Z )'
NZ = '-u Z'
ICC = '( K [,] ( K + 1 ) )'
IOO = '( K (,) ( K + 1 ) )'
FRP = '( b e. RR+ |-> ( b ^c %s ) )' % NZ
DRP = '( b e. RR+ |-> ( %s x. ( b ^c ( %s - 1 ) ) ) )' % (NZ, NZ)
FIC = '( b e. %s |-> ( b ^c %s ) )' % (ICC, NZ)
DIO = '( b e. %s |-> ( %s x. ( b ^c ( %s - 1 ) ) ) )' % (IOO, NZ, NZ)
MB = '( ( abs ` Z ) x. ( K ^c ( -u %s - 1 ) ) )' % RZ
JR = '( %s |`t RR )' % TOP

w = W('cxpmvt', 'The mean-value bound on the difference of two consecutive negative powers.')
A0 = '( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s )' % RZ
kn = w.s([], 'simpll', '( %s -> K e. NN )' % A0)
zc = w.s([], 'simplr', '( %s -> Z e. CC )' % A0)
rzp = w.s([], 'simpr', '( %s -> 0 < %s )' % (A0, RZ))
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
nzc = w.s([zc], 'negcld', '( %s -> %s e. CC )' % (A0, NZ))
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0)
kpos = w.s([kn], 'nngt0d', '( %s -> 0 < K )' % A0)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
onec = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0)
k1r = w.s([kr, r1], 'readdcld', '( %s -> ( K + 1 ) e. RR )' % A0)
sr = w.s([w.s([], 'prid1', 'RR e. { RR , CC }')], 'a1i', '( %s -> RR e. { RR , CC } )' % A0)
# the derivative on the positive reals
Arp = '( %s /\\ b e. RR+ )' % A0
brp = w.s([], 'simpr', '( %s -> b e. RR+ )' % Arp)
bc = w.s([brp], 'rpcnd', '( %s -> b e. CC )' % Arp)
nzcr = w.s([nzc], 'adantr', '( %s -> %s e. CC )' % (Arp, NZ))
acl = w.s([bc, nzcr, w.inst('cxpcl')], 'syl2anc', '( %s -> ( b ^c %s ) e. CC )' % (Arp, NZ))
em1 = w.s([nzcr, w.s([onec], 'adantr', '( %s -> 1 e. CC )' % Arp)], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (Arp, NZ))
bcl = w.s([nzcr, w.s([bc, em1, w.inst('cxpcl')], 'syl2anc', '( %s -> ( b ^c ( %s - 1 ) ) e. CC )' % (Arp, NZ))],
          'mulcld', '( %s -> ( %s x. ( b ^c ( %s - 1 ) ) ) e. CC )' % (Arp, NZ, NZ))
dv1 = w.s([nzc, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, FRP, DRP))
# continuity on RR+
ffrp = w.s([acl, w.s([], 'eqid', '%s = %s' % (FRP, FRP))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, FRP))
fdrp = w.s([bcl, w.s([], 'eqid', '%s = %s' % (DRP, DRP))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, DRP))
dmd = w.s([w.s([dv1], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom %s )' % (A0, FRP, DRP)),
           w.s([fdrp, w.inst('fdm')], 'syl', '( %s -> dom %s = RR+ )' % (A0, DRP))], 'eqtrd',
          '( %s -> dom ( RR _D %s ) = RR+ )' % (A0, FRP))
rrcc = w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0)
rpre = w.s([w.s([], 'rpssre', 'RR+ C_ RR')], 'a1i', '( %s -> RR+ C_ RR )' % A0)
cnrp = w.s([w.s([w.s([rrcc, ffrp, rpre], '3jca', '( %s -> ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) )' % (A0, FRP)), dmd],
                'jca', '( %s -> ( ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) /\\ dom ( RR _D %s ) = RR+ ) )' % (A0, FRP, FRP)),
            w.inst('dvcn')], 'syl', '( %s -> %s e. ( RR+ -cn-> CC ) )' % (A0, FRP))
# ( K [,] ( K + 1 ) ) C_ RR+
Aic = '( %s /\\ b e. %s )' % (A0, ICC)
bic = w.s([], 'simpr', '( %s -> b e. %s )' % (Aic, ICC))
icre = w.s([kr, k1r, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, ICC))
bre = w.s([w.s([icre], 'adantr', '( %s -> %s C_ RR )' % (Aic, ICC)), bic], 'sseldd', '( %s -> b e. RR )' % Aic)
icbi = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc',
           '( %s -> ( b e. %s <-> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) ) )' % (A0, ICC))
icp = w.s([bic, w.s([icbi], 'adantr', '( %s -> ( b e. %s <-> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) ) )' % (Aic, ICC))],
          'mpbid', '( %s -> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) )' % Aic)
kleb = w.s([icp, w.inst('simp2')], 'syl', '( %s -> K <_ b )' % Aic)
bpos = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Aic),
            w.s([kr], 'adantr', '( %s -> K e. RR )' % Aic), bre, w.s([kpos], 'adantr', '( %s -> 0 < K )' % Aic), kleb],
           'ltletrd', '( %s -> 0 < b )' % Aic)
icrp = w.s([w.s([bre, bpos], 'elrpd', '( %s -> b e. RR+ )' % Aic)], 'idi', '( %s -> b e. RR+ )' % Aic)
icssrp = w.s([w.s([icrp], 'ex', '( %s -> ( b e. %s -> b e. RR+ ) )' % (A0, ICC))], 'ssrdv',
             '( %s -> %s C_ RR+ )' % (A0, ICC))
# continuity on the closed interval
resb = w.s([icssrp, w.inst('rescncf')], 'syl',
           '( %s -> ( %s e. ( RR+ -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, FRP, FRP, ICC, ICC))
resc = w.s([cnrp, resb], 'mpd', '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0, FRP, ICC, ICC))
rsm = w.s([icssrp, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, FRP, ICC, FIC))
hF = w.s([w.s([rsm], 'eqcomd', '( %s -> %s = ( %s |` %s ) )' % (A0, FIC, FRP, ICC)), resc], 'eqeltrd',
         '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, FIC, ICC))
# the derivative on the closed interval, with domain the open interval
ejr = w.s([], 'eqid', '%s = %s' % (JR, JR))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
tg = w.s([], 'tgioo4', '%s = %s' % (RETOP, JR))
ntr0 = w.s([kr, k1r, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, RETOP, ICC, IOO))
jeq = w.s([w.s([tg], 'eqcomi', '%s = %s' % (JR, RETOP))], 'a1i', '( %s -> %s = %s )' % (A0, JR, RETOP))
ntr = w.s([w.s([w.s([jeq], 'fveq2d', '( %s -> ( int ` %s ) = ( int ` %s ) )' % (A0, JR, RETOP))], 'fveq1d',
                '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` %s ) ` %s ) )' % (A0, JR, ICC, RETOP, ICC)), ntr0],
          'eqtrd', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, JR, ICC, IOO))
dvic = w.s([sr, acl, bcl, dv1, icssrp, ejr, ek, ntr], 'dvmptres2',
           '( %s -> ( RR _D %s ) = %s )' % (A0, FIC, DIO))
# the domain of that derivative is the open interval
Aio = '( %s /\\ b e. %s )' % (A0, IOO)
bio = w.s([], 'simpr', '( %s -> b e. %s )' % (Aio, IOO))
iossic = w.s([w.s([], 'ioossicc', '%s C_ %s' % (IOO, ICC))], 'a1i', '( %s -> %s C_ %s )' % (A0, IOO, ICC))
iossrp = w.s([iossic, icssrp], 'sstrd', '( %s -> %s C_ RR+ )' % (A0, IOO))
biorp = w.s([w.s([iossrp], 'adantr', '( %s -> %s C_ RR+ )' % (Aio, IOO)), bio], 'sseldd', '( %s -> b e. RR+ )' % Aio)
bcio = w.s([biorp], 'rpcnd', '( %s -> b e. CC )' % Aio)
nzcio = w.s([nzc], 'adantr', '( %s -> %s e. CC )' % (Aio, NZ))
em1io = w.s([nzcio, w.s([onec], 'adantr', '( %s -> 1 e. CC )' % Aio)], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (Aio, NZ))
bclio = w.s([nzcio, w.s([bcio, em1io, w.inst('cxpcl')], 'syl2anc', '( %s -> ( b ^c ( %s - 1 ) ) e. CC )' % (Aio, NZ))],
            'mulcld', '( %s -> ( %s x. ( b ^c ( %s - 1 ) ) ) e. CC )' % (Aio, NZ, NZ))
fdio = w.s([bclio, w.s([], 'eqid', '%s = %s' % (DIO, DIO))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, DIO, IOO))
hD = w.s([w.s([dvic], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom %s )' % (A0, FIC, DIO)),
          w.s([fdio, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A0, DIO, IOO))], 'eqtrd',
         '( %s -> dom ( RR _D %s ) = %s )' % (A0, FIC, IOO))
# the bound on the derivative over the open interval
IOX = '( %s /\\ x e. %s )' % (A0, IOO)
xio = w.s([], 'simpr', '( %s -> x e. %s )' % (IOX, IOO))
xrp = w.s([w.s([iossrp], 'adantr', '( %s -> %s C_ RR+ )' % (IOX, IOO)), xio], 'sseldd', '( %s -> x e. RR+ )' % IOX)
xcc = w.s([xrp], 'rpcnd', '( %s -> x e. CC )' % IOX)
nzx = w.s([nzc], 'adantr', '( %s -> %s e. CC )' % (IOX, NZ))
onex = w.s([onec], 'adantr', '( %s -> 1 e. CC )' % IOX)
em1x = w.s([nzx, onex], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (IOX, NZ))
subx = w.s([], 'oveq1', '( b = x -> ( b ^c ( %s - 1 ) ) = ( x ^c ( %s - 1 ) ) )' % (NZ, NZ))
subx2 = w.s([subx], 'oveq2d',
            '( b = x -> ( %s x. ( b ^c ( %s - 1 ) ) ) = ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (NZ, NZ, NZ, NZ))
vx = mpv(w, IOX, DIO, 'x', '( %s x. ( x ^c ( %s - 1 ) ) )' % (NZ, NZ), subx2, xio,
         vexd(w, IOX, '( %s x. ( x ^c ( %s - 1 ) ) )' % (NZ, NZ)), IOO)
dvx = w.s([w.s([dvic], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (IOX, FIC, DIO))], 'fveq1d',
          '( %s -> ( ( RR _D %s ) ` x ) = ( %s ` x ) )' % (IOX, FIC, DIO))
dvx2 = w.s([dvx, vx], 'eqtrd',
           '( %s -> ( ( RR _D %s ) ` x ) = ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (IOX, FIC, NZ, NZ))
# the modulus of the derivative
ab1 = w.s([nzx, w.s([xcc, em1x, w.inst('cxpcl')], 'syl2anc', '( %s -> ( x ^c ( %s - 1 ) ) e. CC )' % (IOX, NZ))],
          'absmuld',
          '( %s -> ( abs ` ( %s x. ( x ^c ( %s - 1 ) ) ) ) = ( ( abs ` %s ) x. ( abs ` ( x ^c ( %s - 1 ) ) ) ) )' % (IOX, NZ, NZ, NZ, NZ))
abn = w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % IOX)], 'absnegd', '( %s -> ( abs ` %s ) = ( abs ` Z ) )' % (IOX, NZ))
abp = w.s([xrp, em1x, w.inst('abscxp')], 'syl2anc',
          '( %s -> ( abs ` ( x ^c ( %s - 1 ) ) ) = ( x ^c ( Re ` ( %s - 1 ) ) ) )' % (IOX, NZ, NZ))
# ( Re ` ( -u Z - 1 ) ) = ( -u ( Re ` Z ) - 1 )
rex = w.s([w.s([nzx, onex, w.inst('resub')], 'syl2anc',
               '( %s -> ( Re ` ( %s - 1 ) ) = ( ( Re ` %s ) - ( Re ` 1 ) ) )' % (IOX, NZ, NZ)),
           w.s([w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % IOX), w.inst('reneg')], 'syl',
                          '( %s -> ( Re ` %s ) = -u %s )' % (IOX, NZ, RZ))], 'oveq1d',
                    '( %s -> ( ( Re ` %s ) - ( Re ` 1 ) ) = ( -u %s - ( Re ` 1 ) ) )' % (IOX, NZ, RZ)),
               w.s([w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % IOX)], 'oveq2d',
                   '( %s -> ( -u %s - ( Re ` 1 ) ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))], 'eqtrd',
              '( %s -> ( ( Re ` %s ) - ( Re ` 1 ) ) = ( -u %s - 1 ) )' % (IOX, NZ, RZ))], 'eqtrd',
          '( %s -> ( Re ` ( %s - 1 ) ) = ( -u %s - 1 ) )' % (IOX, NZ, RZ))
abp2 = w.s([abp, w.s([rex], 'oveq2d', '( %s -> ( x ^c ( Re ` ( %s - 1 ) ) ) = ( x ^c ( -u %s - 1 ) ) )' % (IOX, NZ, RZ))],
           'eqtrd', '( %s -> ( abs ` ( x ^c ( %s - 1 ) ) ) = ( x ^c ( -u %s - 1 ) ) )' % (IOX, NZ, RZ))
ab2 = w.s([ab1, w.s([abn, abp2], 'oveq12d',
                    '( %s -> ( ( abs ` %s ) x. ( abs ` ( x ^c ( %s - 1 ) ) ) ) = ( ( abs ` Z ) x. ( x ^c ( -u %s - 1 ) ) ) )' % (IOX, NZ, NZ, RZ))],
          'eqtrd', '( %s -> ( abs ` ( %s x. ( x ^c ( %s - 1 ) ) ) ) = ( ( abs ` Z ) x. ( x ^c ( -u %s - 1 ) ) ) )' % (IOX, NZ, NZ, RZ))
# ( -u ( Re ` Z ) - 1 ) = -u ( ( Re ` Z ) + 1 )
rzx = w.s([rz], 'adantr', '( %s -> %s e. RR )' % (IOX, RZ))
negd = w.s([w.s([rzx], 'recnd', '( %s -> %s e. CC )' % (IOX, RZ)), onex], 'negdid',
           '( %s -> -u ( %s + 1 ) = ( -u %s + -u 1 ) )' % (IOX, RZ, RZ))
nsub = w.s([w.s([rzx], 'renegcld', '( %s -> -u %s e. RR )' % (IOX, RZ))], 'recnd', '( %s -> -u %s e. CC )' % (IOX, RZ))
subn = w.s([nsub, onex], 'negsubd', '( %s -> ( -u %s + -u 1 ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))
ee = w.s([negd, subn], 'eqtrd', '( %s -> -u ( %s + 1 ) = ( -u %s - 1 ) )' % (IOX, RZ, RZ))
# the antitone bound
rz1 = w.s([rzx, w.s([r1], 'adantr', '( %s -> 1 e. RR )' % IOX)], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (IOX, RZ))
rz10 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % IOX), rz1,
            w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % IOX), rzx, rz1,
                 w.s([rzp], 'adantr', '( %s -> 0 < %s )' % (IOX, RZ)),
                 w.s([rzx], 'ltp1d', '( %s -> %s < ( %s + 1 ) )' % (IOX, RZ, RZ))], 'lttrd',
                '( %s -> 0 < ( %s + 1 ) )' % (IOX, RZ))], 'ltled', '( %s -> 0 <_ ( %s + 1 ) )' % (IOX, RZ))
kleqx = w.s([w.s([iossic], 'adantr', '( %s -> %s C_ %s )' % (IOX, IOO, ICC)), xio], 'sseldd',
            '( %s -> x e. %s )' % (IOX, ICC))
kx = w.s([w.s([w.s([xio, w.inst('eliooord')], 'syl', '( %s -> ( K < x /\\ x < ( K + 1 ) ) )' % IOX),
               w.inst('simpl')], 'syl', '( %s -> K < x )' % IOX)], 'idi', '( %s -> K < x )' % IOX)
klex = w.s([w.s([kr], 'adantr', '( %s -> K e. RR )' % IOX),
            w.s([xrp], 'rpred', '( %s -> x e. RR )' % IOX), kx], 'ltled', '( %s -> K <_ x )' % IOX)
anti = w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % IOX), xrp, rz1], '3jca',
                '( %s -> ( K e. RR+ /\\ x e. RR+ /\\ ( %s + 1 ) e. RR ) )' % (IOX, RZ)),
            w.s([rz10, klex], 'jca', '( %s -> ( 0 <_ ( %s + 1 ) /\\ K <_ x ) )' % (IOX, RZ)), w.inst('cxpnegle')],
           'syl2anc', '( %s -> ( x ^c -u ( %s + 1 ) ) <_ ( K ^c -u ( %s + 1 ) ) )' % (IOX, RZ, RZ))
anti2 = w.s([w.s([w.s([ee], 'oveq2d', '( %s -> ( x ^c -u ( %s + 1 ) ) = ( x ^c ( -u %s - 1 ) ) )' % (IOX, RZ, RZ))],
                 'eqcomd', '( %s -> ( x ^c ( -u %s - 1 ) ) = ( x ^c -u ( %s + 1 ) ) )' % (IOX, RZ, RZ)), anti], 'eqbrtrd',
            '( %s -> ( x ^c ( -u %s - 1 ) ) <_ ( K ^c -u ( %s + 1 ) ) )' % (IOX, RZ, RZ))
anti3 = w.s([anti2, w.s([ee], 'oveq2d', '( %s -> ( K ^c -u ( %s + 1 ) ) = ( K ^c ( -u %s - 1 ) ) )' % (IOX, RZ, RZ))],
            'breqtrd', '( %s -> ( x ^c ( -u %s - 1 ) ) <_ ( K ^c ( -u %s - 1 ) ) )' % (IOX, RZ, RZ))
nrz1 = w.s([rz1], 'renegcld', '( %s -> -u ( %s + 1 ) e. RR )' % (IOX, RZ))
xnr = w.s([w.s([w.s([xrp, nrz1], 'rpcxpcld', '( %s -> ( x ^c -u ( %s + 1 ) ) e. RR+ )' % (IOX, RZ))], 'rpred',
                '( %s -> ( x ^c -u ( %s + 1 ) ) e. RR )' % (IOX, RZ)),
           w.s([ee], 'oveq2d', '( %s -> ( x ^c -u ( %s + 1 ) ) = ( x ^c ( -u %s - 1 ) ) )' % (IOX, RZ, RZ))],
          'eqeltrrd', '( %s -> ( x ^c ( -u %s - 1 ) ) e. RR )' % (IOX, RZ))
knr = w.s([w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % IOX), nrz1], 'rpcxpcld',
                    '( %s -> ( K ^c -u ( %s + 1 ) ) e. RR+ )' % (IOX, RZ))], 'rpred',
                '( %s -> ( K ^c -u ( %s + 1 ) ) e. RR )' % (IOX, RZ)),
           w.s([ee], 'oveq2d', '( %s -> ( K ^c -u ( %s + 1 ) ) = ( K ^c ( -u %s - 1 ) ) )' % (IOX, RZ, RZ))],
          'eqeltrrd', '( %s -> ( K ^c ( -u %s - 1 ) ) e. RR )' % (IOX, RZ))
absz = w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % IOX)], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % IOX)
absz0 = w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % IOX)], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % IOX)
mulb = w.s([xnr, knr, w.s([absz, absz0], 'jca', '( %s -> ( ( abs ` Z ) e. RR /\\ 0 <_ ( abs ` Z ) ) )' % IOX)],
           '3jca', '( %s -> ( ( x ^c ( -u %s - 1 ) ) e. RR /\\ ( K ^c ( -u %s - 1 ) ) e. RR /\\ ( ( abs ` Z ) e. RR /\\ 0 <_ ( abs ` Z ) ) ) )' % (IOX, RZ, RZ))
le5 = w.s([mulb, anti3, w.inst('lemul2a')], 'syl2anc',
          '( %s -> ( ( abs ` Z ) x. ( x ^c ( -u %s - 1 ) ) ) <_ ( ( abs ` Z ) x. ( K ^c ( -u %s - 1 ) ) ) )' % (IOX, RZ, RZ))
hL = w.s([w.s([dvx2], 'fveq2d', '( %s -> ( abs ` ( ( RR _D %s ) ` x ) ) = ( abs ` ( %s x. ( x ^c ( %s - 1 ) ) ) ) )' % (IOX, FIC, NZ, NZ)),
          w.s([ab2, le5], 'eqbrtrd',
              '( %s -> ( abs ` ( %s x. ( x ^c ( %s - 1 ) ) ) ) <_ %s )' % (IOX, NZ, NZ, MB))], 'eqbrtrd',
         '( %s -> ( abs ` ( ( RR _D %s ) ` x ) ) <_ %s )' % (IOX, FIC, MB))
nrzr = w.s([rz], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))
hM = w.s([w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0),
          w.s([w.s([krp, w.s([nrzr, r1], 'resubcld', '( %s -> ( -u %s - 1 ) e. RR )' % (A0, RZ))], 'rpcxpcld',
                   '( %s -> ( K ^c ( -u %s - 1 ) ) e. RR+ )' % (A0, RZ))], 'rpred',
              '( %s -> ( K ^c ( -u %s - 1 ) ) e. RR )' % (A0, RZ))], 'remulcld', '( %s -> %s e. RR )' % (A0, MB))
# the Lipschitz bound at the endpoints
kic = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc',
          '( %s -> ( K e. %s <-> ( K e. RR /\\ K <_ K /\\ K <_ ( K + 1 ) ) ) )' % (A0, ICC))
kle1 = w.s([kr, k1r, w.s([kr], 'ltp1d', '( %s -> K < ( K + 1 ) )' % A0)], 'ltled', '( %s -> K <_ ( K + 1 ) )' % A0)
kmem = w.s([w.s([kr, w.s([kr], 'leidd', '( %s -> K <_ K )' % A0), kle1], '3jca',
                '( %s -> ( K e. RR /\\ K <_ K /\\ K <_ ( K + 1 ) ) )' % A0), kic], 'mpbird',
           '( %s -> K e. %s )' % (A0, ICC))
k1ic = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc',
           '( %s -> ( ( K + 1 ) e. %s <-> ( ( K + 1 ) e. RR /\\ K <_ ( K + 1 ) /\\ ( K + 1 ) <_ ( K + 1 ) ) ) )' % (A0, ICC))
k1mem = w.s([w.s([k1r, kle1, w.s([k1r], 'leidd', '( %s -> ( K + 1 ) <_ ( K + 1 ) )' % A0)], '3jca',
                 '( %s -> ( ( K + 1 ) e. RR /\\ K <_ ( K + 1 ) /\\ ( K + 1 ) <_ ( K + 1 ) ) )' % A0), k1ic],
            'mpbird', '( %s -> ( K + 1 ) e. %s )' % (A0, ICC))
lip = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'idi', '( %s -> %s )' % (A0, A0)),
           w.s([k1mem, kmem], 'jca', '( %s -> ( ( K + 1 ) e. %s /\\ K e. %s ) )' % (A0, ICC, ICC))], 'jca',
          '( %s -> ( %s /\\ ( ( K + 1 ) e. %s /\\ K e. %s ) ) )' % (A0, A0, ICC, ICC))
dvl = w.s([kr, k1r, hF, hD, hM, hL], 'dvlip',
          '( ( %s /\\ ( ( K + 1 ) e. %s /\\ K e. %s ) ) -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ ( %s x. ( abs ` ( ( K + 1 ) - K ) ) ) )' % (A0, ICC, ICC, FIC, FIC, MB))
dvl2 = w.s([lip, dvl], 'mpdan' if False else 'syl', '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ ( %s x. ( abs ` ( ( K + 1 ) - K ) ) ) )' % (A0, FIC, FIC, MB))
# the values at the endpoints and the unit gap
subk = w.s([], 'oveq1', '( b = K -> ( b ^c %s ) = ( K ^c %s ) )' % (NZ, NZ))
vK = mpv(w, A0, FIC, 'K', '( K ^c %s )' % NZ, subk, kmem, vexd(w, A0, '( K ^c %s )' % NZ), ICC)
subk1 = w.s([], 'oveq1', '( b = ( K + 1 ) -> ( b ^c %s ) = ( ( K + 1 ) ^c %s ) )' % (NZ, NZ))
vK1 = mpv(w, A0, FIC, '( K + 1 )', '( ( K + 1 ) ^c %s )' % NZ, subk1, k1mem,
          vexd(w, A0, '( ( K + 1 ) ^c %s )' % NZ), ICC)
gap = w.s([w.s([kr], 'recnd', '( %s -> K e. CC )' % A0), onec], 'pncan2d', '( %s -> ( ( K + 1 ) - K ) = 1 )' % A0)
gap2 = w.s([w.s([gap], 'fveq2d', '( %s -> ( abs ` ( ( K + 1 ) - K ) ) = ( abs ` 1 ) )' % A0),
            w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % A0)], 'eqtrd',
           '( %s -> ( abs ` ( ( K + 1 ) - K ) ) = 1 )' % A0)
rhs = w.s([w.s([gap2], 'oveq2d', '( %s -> ( %s x. ( abs ` ( ( K + 1 ) - K ) ) ) = ( %s x. 1 ) )' % (A0, MB, MB)),
           w.s([w.s([hM], 'recnd', '( %s -> %s e. CC )' % (A0, MB))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A0, MB, MB))],
          'eqtrd', '( %s -> ( %s x. ( abs ` ( ( K + 1 ) - K ) ) ) = %s )' % (A0, MB, MB))
lhs = w.s([w.s([vK1, vK], 'oveq12d',
                '( %s -> ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) = ( ( ( K + 1 ) ^c %s ) - ( K ^c %s ) ) )' % (A0, FIC, FIC, NZ, NZ))],
          'fveq2d', '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) = ( abs ` ( ( ( K + 1 ) ^c %s ) - ( K ^c %s ) ) ) )' % (A0, FIC, FIC, NZ, NZ))
step = w.s([w.s([lhs], 'eqcomd',
                '( %s -> ( abs ` ( ( ( K + 1 ) ^c %s ) - ( K ^c %s ) ) ) = ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) )' % (A0, NZ, NZ, FIC, FIC)),
            w.s([dvl2, rhs], 'breqtrd',
                '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ %s )' % (A0, FIC, FIC, MB))], 'eqbrtrd',
           '( %s -> ( abs ` ( ( ( K + 1 ) ^c %s ) - ( K ^c %s ) ) ) <_ %s )' % (A0, NZ, NZ, MB))
kcx = w.s([w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0), nzc, w.inst('cxpcl')], 'syl2anc',
          '( %s -> ( K ^c %s ) e. CC )' % (A0, NZ))
k1cx = w.s([w.s([w.s([kr, r1], 'readdcld', '( %s -> ( K + 1 ) e. RR )' % A0)], 'recnd', '( %s -> ( K + 1 ) e. CC )' % A0),
            nzc, w.inst('cxpcl')], 'syl2anc', '( %s -> ( ( K + 1 ) ^c %s ) e. CC )' % (A0, NZ))
w.qed([w.s([kcx, k1cx], 'abssubd',
           '( %s -> ( abs ` ( ( K ^c %s ) - ( ( K + 1 ) ^c %s ) ) ) = ( abs ` ( ( ( K + 1 ) ^c %s ) - ( K ^c %s ) ) ) )' % (A0, NZ, NZ, NZ, NZ)),
       step], 'eqbrtrd',
      '( %s -> ( abs ` ( ( K ^c %s ) - ( ( K + 1 ) ^c %s ) ) ) <_ %s )' % (A0, NZ, NZ, MB)); run3(w)
