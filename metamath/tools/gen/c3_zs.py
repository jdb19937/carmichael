"""Sortie C3 section 4: the zeta majorant (the integral comparison)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

PW = '( x ^c ( 1 - T ) )'
AMP = '( x e. RR+ |-> ( %s / ( 1 - T ) ) )' % PW
BMP = '( x e. RR+ |-> ( x ^c -u T ) )'
DEC = '( ( 1 - T ) x. ( x ^c ( ( 1 - T ) - 1 ) ) )'

# ---- cxpnegle --------------------------------------------------------------
w = W('cxpnegle', 'A negative power of a positive real is antitone in the base.')
A0 = '( ( X e. RR+ /\\ Y e. RR+ /\\ T e. RR ) /\\ ( 0 <_ T /\\ X <_ Y ) )'
xr = w.s([], 'simpl1', '( %s -> X e. RR+ )' % A0)
yr = w.s([], 'simpl2', '( %s -> Y e. RR+ )' % A0)
tr = w.s([], 'simpl3', '( %s -> T e. RR )' % A0)
t0 = w.s([], 'simprl', '( %s -> 0 <_ T )' % A0)
xy = w.s([], 'simprr', '( %s -> X <_ Y )' % A0)
xrr = w.s([xr], 'rpred', '( %s -> X e. RR )' % A0); yrr = w.s([yr], 'rpred', '( %s -> Y e. RR )' % A0)
x0 = w.s([xr], 'rpge0d', '( %s -> 0 <_ X )' % A0)
pxp = w.s([xr, tr, w.inst('rpcxpcl')], 'syl2anc', '( %s -> ( X ^c T ) e. RR+ )' % A0)
pyp = w.s([yr, tr, w.inst('rpcxpcl')], 'syl2anc', '( %s -> ( Y ^c T ) e. RR+ )' % A0)
le = w.s([w.s([xrr, yrr, tr], '3jca', '( %s -> ( X e. RR /\\ Y e. RR /\\ T e. RR ) )' % A0),
          w.s([x0, t0], 'jca', '( %s -> ( 0 <_ X /\\ 0 <_ T ) )' % A0), xy, w.inst('cxple2a')], 'syl3anc',
         '( %s -> ( X ^c T ) <_ ( Y ^c T ) )' % A0)
lx = w.s([w.s([pxp], 'rpred', '( %s -> ( X ^c T ) e. RR )' % A0), w.s([pxp], 'rpgt0d', '( %s -> 0 < ( X ^c T ) )' % A0)],
         'jca', '( %s -> ( ( X ^c T ) e. RR /\\ 0 < ( X ^c T ) ) )' % A0)
ly = w.s([w.s([pyp], 'rpred', '( %s -> ( Y ^c T ) e. RR )' % A0), w.s([pyp], 'rpgt0d', '( %s -> 0 < ( Y ^c T ) )' % A0)],
         'jca', '( %s -> ( ( Y ^c T ) e. RR /\\ 0 < ( Y ^c T ) ) )' % A0)
bi = w.s([lx, ly, w.inst('lerec')], 'syl2anc',
         '( %s -> ( ( X ^c T ) <_ ( Y ^c T ) <-> ( 1 / ( Y ^c T ) ) <_ ( 1 / ( X ^c T ) ) ) )' % A0)
rl = w.s([le, bi], 'mpbid', '( %s -> ( 1 / ( Y ^c T ) ) <_ ( 1 / ( X ^c T ) ) )' % A0)
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
ey = w.s([w.s([yr], 'rpcnd', '( %s -> Y e. CC )' % A0), w.s([yr], 'rpne0d', '( %s -> Y =/= 0 )' % A0), tc,
          w.inst('cxpneg')], 'syl3anc', '( %s -> ( Y ^c -u T ) = ( 1 / ( Y ^c T ) ) )' % A0)
ex = w.s([w.s([xr], 'rpcnd', '( %s -> X e. CC )' % A0), w.s([xr], 'rpne0d', '( %s -> X =/= 0 )' % A0), tc,
          w.inst('cxpneg')], 'syl3anc', '( %s -> ( X ^c -u T ) = ( 1 / ( X ^c T ) ) )' % A0)
s1 = w.s([ey, rl], 'eqbrtrd', '( %s -> ( Y ^c -u T ) <_ ( 1 / ( X ^c T ) ) )' % A0)
w.qed([s1, w.s([ex], 'eqcomd', '( %s -> ( 1 / ( X ^c T ) ) = ( X ^c -u T ) )' % A0)], 'breqtrd',
      '( %s -> ( Y ^c -u T ) <_ ( X ^c -u T ) )' % A0); run3(w)

# ---- cxpdvrp ---------------------------------------------------------------
w = W('cxpdvrp', 'The primitive of the zeta integrand on the positive reals.')
A0 = '( T e. RR /\\ 1 < T )'
A1 = '( %s /\\ x e. RR+ )' % A0
tr = w.s([], 'simpl', '( %s -> T e. RR )' % A0)
t1 = w.s([], 'simpr', '( %s -> 1 < T )' % A0)
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
onec = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
mtc = w.s([onec, tc], 'subcld', '( %s -> ( 1 - T ) e. CC )' % A0)
mtne = w.s([onec, tc, w.s([t1], 'ltned', '( %s -> 1 =/= T )' % A0)], 'subne0d',
           '( %s -> ( 1 - T ) =/= 0 )' % A0)
dv1 = w.s([mtc, w.inst('dvcxp1')], 'syl',
          '( %s -> ( RR _D ( x e. RR+ |-> %s ) ) = ( x e. RR+ |-> %s ) )' % (A0, PW, DEC))
xrp = w.s([], 'simpr', '( %s -> x e. RR+ )' % A1)
xc = w.s([xrp], 'rpcnd', '( %s -> x e. CC )' % A1)
mtc1 = w.s([mtc], 'adantr', '( %s -> ( 1 - T ) e. CC )' % A1)
onec1 = w.s([onec], 'adantr', '( %s -> 1 e. CC )' % A1)
acl = w.s([xc, mtc1, w.inst('cxpcl')], 'syl2anc', '( %s -> %s e. CC )' % (A1, PW))
ec = w.s([mtc1, onec1], 'subcld', '( %s -> ( ( 1 - T ) - 1 ) e. CC )' % A1)
pcl = w.s([xc, ec, w.inst('cxpcl')], 'syl2anc', '( %s -> ( x ^c ( ( 1 - T ) - 1 ) ) e. CC )' % A1)
bcl = w.s([mtc1, pcl], 'mulcld', '( %s -> %s e. CC )' % (A1, DEC))
sr = w.s([w.s([], 'prid1', 'RR e. { RR , CC }')], 'a1i', '( %s -> RR e. { RR , CC } )' % A0)
dv2 = w.s([sr, acl, bcl, dv1, mtc, mtne], 'dvmptdivc',
          '( %s -> ( RR _D %s ) = ( x e. RR+ |-> ( %s / ( 1 - T ) ) ) )' % (A0, AMP, DEC))
# ( ( 1 - T ) - 1 ) = -u T
s32 = w.s([onec, tc, onec], 'sub32d', '( %s -> ( ( 1 - T ) - 1 ) = ( ( 1 - 1 ) - T ) )' % A0)
z0 = w.s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( %s -> ( 1 - 1 ) = 0 )' % A0)
s33 = w.s([s32, w.s([z0], 'oveq1d', '( %s -> ( ( 1 - 1 ) - T ) = ( 0 - T ) )' % A0)], 'eqtrd',
          '( %s -> ( ( 1 - T ) - 1 ) = ( 0 - T ) )' % A0)
dn = w.s([w.s([w.s([], 'df-neg', '-u T = ( 0 - T )')], 'eqcomi', '( 0 - T ) = -u T')], 'a1i',
         '( %s -> ( 0 - T ) = -u T )' % A0)
expe = w.s([s33, dn], 'eqtrd', '( %s -> ( ( 1 - T ) - 1 ) = -u T )' % A0)
expe1 = w.s([expe], 'adantr', '( %s -> ( ( 1 - T ) - 1 ) = -u T )' % A1)
pe = w.s([expe1], 'oveq2d', '( %s -> ( x ^c ( ( 1 - T ) - 1 ) ) = ( x ^c -u T ) )' % A1)
cn3 = w.s([pcl, mtc1, w.s([mtne], 'adantr', '( %s -> ( 1 - T ) =/= 0 )' % A1)], 'divcan3d',
          '( %s -> ( %s / ( 1 - T ) ) = ( x ^c ( ( 1 - T ) - 1 ) ) )' % (A1, DEC))
body = w.s([cn3, pe], 'eqtrd', '( %s -> ( %s / ( 1 - T ) ) = ( x ^c -u T ) )' % (A1, DEC))
mpe = w.s([body], 'mpteq2dva', '( %s -> ( x e. RR+ |-> ( %s / ( 1 - T ) ) ) = %s )' % (A0, DEC, BMP))
w.qed([dv2, mpe], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, AMP, BMP)); run3(w)

# ---- cxpdvio ---------------------------------------------------------------
JR = '( %s |`t RR )' % TOP
IOO = '( M (,) N )'
AIO = '( x e. %s |-> ( %s / ( 1 - T ) ) )' % (IOO, PW)
BIO = '( x e. %s |-> ( x ^c -u T ) )' % IOO
w = W('cxpdvio', 'The primitive of the zeta integrand on an open interval of positive reals.')
A0 = '( ( T e. RR /\\ 1 < T ) /\\ ( M e. RR /\\ 0 <_ M /\\ N e. RR ) )'
A1 = '( %s /\\ x e. RR+ )' % A0
A2 = '( %s /\\ x e. %s )' % (A0, IOO)
tt = w.s([], 'simpl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
mr = w.s([], 'simpr1', '( %s -> M e. RR )' % A0)
m0 = w.s([], 'simpr2', '( %s -> 0 <_ M )' % A0)
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
onec = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0)
mtc = w.s([onec, tc], 'subcld', '( %s -> ( 1 - T ) e. CC )' % A0)
xrp = w.s([], 'simpr', '( %s -> x e. RR+ )' % A1)
xc = w.s([xrp], 'rpcnd', '( %s -> x e. CC )' % A1)
mtc1 = w.s([mtc], 'adantr', '( %s -> ( 1 - T ) e. CC )' % A1)
t1a = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 1 < T )' % A0)
r1a = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
mtne = w.s([onec, tc, w.s([t1a], 'ltned', '( %s -> 1 =/= T )' % A0)], 'subne0d', '( %s -> ( 1 - T ) =/= 0 )' % A0)
mtne1 = w.s([mtne], 'adantr', '( %s -> ( 1 - T ) =/= 0 )' % A1)
acl = w.s([w.s([xc, mtc1, w.inst('cxpcl')], 'syl2anc', '( %s -> %s e. CC )' % (A1, PW)), mtc1, mtne1], 'divcld',
          '( %s -> ( %s / ( 1 - T ) ) e. CC )' % (A1, PW))
bcl = w.s([xc, w.s([w.s([tc], 'negcld', '( %s -> -u T e. CC )' % A0)], 'adantr', '( %s -> -u T e. CC )' % A1),
           w.inst('cxpcl')], 'syl2anc', '( %s -> ( x ^c -u T ) e. CC )' % A1)
sr = w.s([w.s([], 'prid1', 'RR e. { RR , CC }')], 'a1i', '( %s -> RR e. { RR , CC } )' % A0)
dvr = w.s([tt, w.inst('cxpdvrp')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, AMP, BMP))
# ( M (,) N ) C_ RR+
xio = w.s([], 'simpr', '( %s -> x e. %s )' % (A2, IOO))
xre = w.s([xio, w.inst('elioore')], 'syl', '( %s -> x e. RR )' % A2)
ord = w.s([xio, w.inst('eliooord')], 'syl', '( %s -> ( M < x /\\ x < N ) )' % A2)
mlt = w.s([ord, w.inst('simpl')], 'syl', '( %s -> M < x )' % A2)
xpos = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A2),
            w.s([mr], 'adantr', '( %s -> M e. RR )' % A2), xre,
            w.s([m0], 'adantr', '( %s -> 0 <_ M )' % A2), mlt], 'lelttrd', '( %s -> 0 < x )' % A2)
xel = w.s([xre, xpos], 'elrpd', '( %s -> x e. RR+ )' % A2)
ssrp = w.s([w.s([xel], 'ex', '( %s -> ( x e. %s -> x e. RR+ ) )' % (A0, IOO))], 'ssrdv',
           '( %s -> %s C_ RR+ )' % (A0, IOO))
ejr = w.s([], 'eqid', '%s = %s' % (JR, JR))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
iot = w.s([w.s([w.s([], 'iooretop', '%s e. %s' % (IOO, RETOP)),
                w.s([], 'tgioo4', '%s = %s' % (RETOP, JR))], 'eleqtri', '%s e. %s' % (IOO, JR))], 'a1i',
          '( %s -> %s e. %s )' % (A0, IOO, JR))
w.qed([sr, acl, bcl, dvr, ssrp, ejr, ek, iot], 'dvmptres',
      '( %s -> ( RR _D %s ) = %s )' % (A0, AIO, BIO)); run3(w)

# ---- zserfz ----------------------------------------------------------------
ICC = '( M [,] N )'
AIC = '( x e. %s |-> ( %s / ( 1 - T ) ) )' % (ICC, PW)
PM = '( M ^c ( 1 - T ) )'; PN = '( N ^c ( 1 - T ) )'
SLIT = '( CC \\ ( -oo (,] 0 ) )'
w = W('zserfz', 'The integral comparison for the zeta series: a partial sum of the tail is below the integral.')
A0 = '( ( T e. RR /\\ 1 < T ) /\\ ( M e. NN /\\ N e. ( ZZ>= ` M ) ) )'
Aic = '( %s /\\ x e. %s )' % (A0, ICC)
Aio = '( %s /\\ x e. %s )' % (A0, IOO)
Afo = '( %s /\\ k e. ( M ..^ N ) )' % A0
Afl = '( %s /\\ ( k e. ( M ..^ N ) /\\ x e. ( k (,) ( k + 1 ) ) ) )' % A0
tt = w.s([], 'simpl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
t1 = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 1 < T )' % A0)
mn = w.s([], 'simprl', '( %s -> M e. NN )' % A0)
nu = w.s([], 'simprr', '( %s -> N e. ( ZZ>= ` M ) )' % A0)
nz = w.s([nu, w.inst('eluzelz')], 'syl', '( %s -> N e. ZZ )' % A0)
nr = w.s([nz], 'zred', '( %s -> N e. RR )' % A0)
mr = w.s([mn], 'nnred', '( %s -> M e. RR )' % A0)
mrp = w.s([mn], 'nnrpd', '( %s -> M e. RR+ )' % A0)
mpos = w.s([mn], 'nngt0d', '( %s -> 0 < M )' % A0)
m0 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), mr, mpos], 'ltled',
         '( %s -> 0 <_ M )' % A0)
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
onec = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0)
mtr = w.s([r1, tr], 'resubcld', '( %s -> ( 1 - T ) e. RR )' % A0)
mtc = w.s([onec, tc], 'subcld', '( %s -> ( 1 - T ) e. CC )' % A0)
mtne = w.s([onec, tc, w.s([t1], 'ltned', '( %s -> 1 =/= T )' % A0)], 'subne0d', '( %s -> ( 1 - T ) =/= 0 )' % A0)
tm1 = w.s([tr, r1], 'resubcld', '( %s -> ( T - 1 ) e. RR )' % A0)
tm1pos = w.s([t1, w.s([r1, tr], 'posdifd', '( %s -> ( 1 < T <-> 0 < ( T - 1 ) ) )' % A0)], 'mpbid',
             '( %s -> 0 < ( T - 1 ) )' % A0)
tm1rp = w.s([tm1, tm1pos], 'elrpd', '( %s -> ( T - 1 ) e. RR+ )' % A0)
tge0 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), r1, tr,
            w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A0), t1], 'lelttrd', '( %s -> 0 < T )' % A0)
tge0b = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), tr, tge0], 'ltled',
            '( %s -> 0 <_ T )' % A0)
# ( M [,] N ) C_ ( CC \ ( -oo (,] 0 ) ) and each point is in RR+
xic = w.s([], 'simpr', '( %s -> x e. %s )' % (Aic, ICC))
icre = w.s([mr, nr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, ICC))
xre = w.s([w.s([icre], 'adantr', '( %s -> %s C_ RR )' % (Aic, ICC)), xic], 'sseldd', '( %s -> x e. RR )' % Aic)
icbi = w.s([mr, nr, w.inst('elicc2')], 'syl2anc',
           '( %s -> ( x e. %s <-> ( x e. RR /\\ M <_ x /\\ x <_ N ) ) )' % (A0, ICC))
icp = w.s([xic, w.s([icbi], 'adantr', '( %s -> ( x e. %s <-> ( x e. RR /\\ M <_ x /\\ x <_ N ) ) )' % (Aic, ICC))],
          'mpbid', '( %s -> ( x e. RR /\\ M <_ x /\\ x <_ N ) )' % Aic)
mlex = w.s([icp, w.inst('simp2')], 'syl', '( %s -> M <_ x )' % Aic)
xpos = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Aic),
            w.s([mr], 'adantr', '( %s -> M e. RR )' % Aic), xre,
            w.s([mpos], 'adantr', '( %s -> 0 < M )' % Aic), mlex], 'ltletrd', '( %s -> 0 < x )' % Aic)
xrp = w.s([xre, xpos], 'elrpd', '( %s -> x e. RR+ )' % Aic)
xcc = w.s([xrp], 'rpcnd', '( %s -> x e. CC )' % Aic)
xrex = w.s([xre, w.inst('rere')], 'syl', '( %s -> ( Re ` x ) = x )' % Aic)
xrepos = w.s([xpos, xrex], 'breqtrrd', '( %s -> 0 < ( Re ` x ) )' % Aic)
xslit = w.s([xcc, xrepos, w.inst('elslitre')], 'syl2anc', '( %s -> x e. %s )' % (Aic, SLIT))
icss = w.s([w.s([xslit], 'ex', '( %s -> ( x e. %s -> x e. %s ) )' % (A0, ICC, SLIT))], 'ssrdv',
           '( %s -> %s C_ %s )' % (A0, ICC, SLIT))
# ( M [,] N ) C_ RR+ from the same pointwise argument
icsrp = w.s([w.s([xrp], 'ex', '( %s -> ( x e. %s -> x e. RR+ ) )' % (A0, ICC))], 'ssrdv',
            '( %s -> %s C_ RR+ )' % (A0, ICC))
# the primitive is real-valued and differentiable on RR+, hence continuous there
Arp = '( %s /\\ x e. RR+ )' % A0
xrpv = w.s([], 'simpr', '( %s -> x e. RR+ )' % Arp)
pwrpv = w.s([xrpv, w.s([mtr], 'adantr', '( %s -> ( 1 - T ) e. RR )' % Arp)], 'rpcxpcld',
            '( %s -> %s e. RR+ )' % (Arp, PW))
qrev = w.s([w.s([pwrpv], 'rpred', '( %s -> %s e. RR )' % (Arp, PW)),
            w.s([mtr], 'adantr', '( %s -> ( 1 - T ) e. RR )' % Arp),
            w.s([mtne], 'adantr', '( %s -> ( 1 - T ) =/= 0 )' % Arp)], 'redivcld',
           '( %s -> ( %s / ( 1 - T ) ) e. RR )' % (Arp, PW))
qfrp = w.s([w.s([qrev], 'recnd', '( %s -> ( %s / ( 1 - T ) ) e. CC )' % (Arp, PW)),
            w.s([], 'eqid', '%s = %s' % (AMP, AMP))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, AMP))
dvrp = w.s([tt, w.inst('cxpdvrp')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, AMP, BMP))
bfrp = w.s([w.s([xrpv, w.s([w.s([w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)], 'adantr',
                                '( %s -> -u T e. RR )' % Arp)], 'idi', '( %s -> -u T e. RR )' % Arp)],
                'rpcxpcld', '( %s -> ( x ^c -u T ) e. RR+ )' % Arp)], 'rpcnd',
           '( %s -> ( x ^c -u T ) e. CC )' % Arp)
bfn = w.s([bfrp, w.s([], 'eqid', '%s = %s' % (BMP, BMP))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, BMP))
dmb = w.s([bfn, w.inst('fdm')], 'syl', '( %s -> dom %s = RR+ )' % (A0, BMP))
dmd = w.s([w.s([dvrp], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom %s )' % (A0, AMP, BMP)), dmb], 'eqtrd',
          '( %s -> dom ( RR _D %s ) = RR+ )' % (A0, AMP))
rpcc = w.s([w.s([], 'rpssre', 'RR+ C_ RR')], 'a1i', '( %s -> RR+ C_ RR )' % A0)
rrcc = w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0)
cnrp = w.s([w.s([w.s([rrcc, qfrp, rpcc], '3jca', '( %s -> ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) )' % (A0, AMP)),
                 dmd], 'jca',
                '( %s -> ( ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) /\\ dom ( RR _D %s ) = RR+ ) )' % (A0, AMP, AMP)),
            w.inst('dvcn')], 'syl', '( %s -> %s e. ( RR+ -cn-> CC ) )' % (A0, AMP))
resb = w.s([icsrp, w.inst('rescncf')], 'syl', '( %s -> ( %s e. ( RR+ -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, AMP, AMP, ICC, ICC))
resc = w.s([cnrp, resb], 'mpd', '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0, AMP, ICC, ICC))
rsm = w.s([icsrp, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, AMP, ICC, AIC))
qcn = w.s([w.s([rsm], 'eqcomd', '( %s -> %s = ( %s |` %s ) )' % (A0, AIC, AMP, ICC)), resc], 'eqeltrd',
          '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, AIC, ICC))
# the primitive is real-valued on the closed interval
pwrp = w.s([xrp, w.s([mtr], 'adantr', '( %s -> ( 1 - T ) e. RR )' % Aic)], 'rpcxpcld', '( %s -> %s e. RR+ )' % (Aic, PW))
qre = w.s([w.s([pwrp], 'rpred', '( %s -> %s e. RR )' % (Aic, PW)), w.s([mtr], 'adantr', '( %s -> ( 1 - T ) e. RR )' % Aic),
           w.s([mtne], 'adantr', '( %s -> ( 1 - T ) =/= 0 )' % Aic)], 'redivcld',
          '( %s -> ( %s / ( 1 - T ) ) e. RR )' % (Aic, PW))
qf = w.s([qre, w.s([], 'eqid', '%s = %s' % (AIC, AIC))], 'fmptd', '( %s -> %s : %s --> RR )' % (A0, AIC, ICC))
cdm = w.s([rrcc, qcn, w.inst('cncfcdm')], 'syl2anc',
          '( %s -> ( %s e. ( %s -cn-> RR ) <-> %s : %s --> RR ) )' % (A0, AIC, ICC, AIC, ICC))
hA = w.s([qf, cdm], 'mpbird', '( %s -> %s e. ( %s -cn-> RR ) )' % (A0, AIC, ICC))
# the integrand is real on the open interval
xio = w.s([], 'simpr', '( %s -> x e. %s )' % (Aio, IOO))
xior = w.s([xio, w.inst('elioore')], 'syl', '( %s -> x e. RR )' % Aio)
iord = w.s([xio, w.inst('eliooord')], 'syl', '( %s -> ( M < x /\\ x < N ) )' % Aio)
xiop = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Aio),
            w.s([mr], 'adantr', '( %s -> M e. RR )' % Aio), xior,
            w.s([m0], 'adantr', '( %s -> 0 <_ M )' % Aio),
            w.s([iord, w.inst('simpl')], 'syl', '( %s -> M < x )' % Aio)], 'lelttrd', '( %s -> 0 < x )' % Aio)
xiorp = w.s([xior, xiop], 'elrpd', '( %s -> x e. RR+ )' % Aio)
hV = w.s([xiorp, w.s([w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)], 'adantr', '( %s -> -u T e. RR )' % Aio)],
         'rpcxpcld', '( %s -> ( x ^c -u T ) e. RR+ )' % Aio)
hVr = w.s([hV], 'rpred', '( %s -> ( x ^c -u T ) e. RR )' % Aio)
# the derivative
hB = w.s([w.s([tt, w.s([mr, m0, nr], '3jca', '( %s -> ( M e. RR /\\ 0 <_ M /\\ N e. RR ) )' % A0)], 'jca',
              '( %s -> ( ( T e. RR /\\ 1 < T ) /\\ ( M e. RR /\\ 0 <_ M /\\ N e. RR ) ) )' % A0),
          w.inst('cxpdvio')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, AIO, BIO))
# the endpoint substitutions
hC = w.s([w.s([], 'oveq1', '( x = M -> %s = %s )' % (PW, PM))], 'oveq1d',
         '( x = M -> ( %s / ( 1 - T ) ) = ( %s / ( 1 - T ) ) )' % (PW, PM))
hD = w.s([w.s([], 'oveq1', '( x = N -> %s = %s )' % (PW, PN))], 'oveq1d',
         '( x = N -> ( %s / ( 1 - T ) ) = ( %s / ( 1 - T ) ) )' % (PW, PN))
# the summand
kfo = w.s([], 'simpr', '( %s -> k e. ( M ..^ N ) )' % Afo)
kz = w.s([kfo, w.inst('elfzoelz')], 'syl', '( %s -> k e. ZZ )' % Afo)
kr = w.s([kz], 'zred', '( %s -> k e. RR )' % Afo)
kge = w.s([kfo, w.inst('elfzole1')], 'syl', '( %s -> M <_ k )' % Afo)
k1p = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Afo),
           w.s([mr], 'adantr', '( %s -> M e. RR )' % Afo), kr,
           w.s([mpos], 'adantr', '( %s -> 0 < M )' % Afo), kge], 'ltletrd', '( %s -> 0 < k )' % Afo)
kp1r = w.s([kr, w.s([r1], 'adantr', '( %s -> 1 e. RR )' % Afo)], 'readdcld', '( %s -> ( k + 1 ) e. RR )' % Afo)
kp1p = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Afo), kr, kp1r, k1p,
            w.s([kr], 'ltp1d', '( %s -> k < ( k + 1 ) )' % Afo)], 'lttrd', '( %s -> 0 < ( k + 1 ) )' % Afo)
kp1rp = w.s([kp1r, kp1p], 'elrpd', '( %s -> ( k + 1 ) e. RR+ )' % Afo)
hX = w.s([w.s([kp1rp, w.s([w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)], 'adantr', '( %s -> -u T e. RR )' % Afo)],
               'rpcxpcld', '( %s -> ( ( k + 1 ) ^c -u T ) e. RR+ )' % Afo)], 'rpred',
         '( %s -> ( ( k + 1 ) ^c -u T ) e. RR )' % Afo)
# the monotonicity on each subinterval
kfl = w.s([], 'simprl', '( %s -> k e. ( M ..^ N ) )' % Afl)
xfl = w.s([], 'simprr', '( %s -> x e. ( k (,) ( k + 1 ) ) )' % Afl)
kflz = w.s([kfl, w.inst('elfzoelz')], 'syl', '( %s -> k e. ZZ )' % Afl)
kflr = w.s([kflz], 'zred', '( %s -> k e. RR )' % Afl)
kflge = w.s([kfl, w.inst('elfzole1')], 'syl', '( %s -> M <_ k )' % Afl)
kflp = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Afl),
            w.s([mr], 'adantr', '( %s -> M e. RR )' % Afl), kflr,
            w.s([mpos], 'adantr', '( %s -> 0 < M )' % Afl), kflge], 'ltletrd', '( %s -> 0 < k )' % Afl)
xflr = w.s([xfl, w.inst('elioore')], 'syl', '( %s -> x e. RR )' % Afl)
xflo = w.s([xfl, w.inst('eliooord')], 'syl', '( %s -> ( k < x /\\ x < ( k + 1 ) ) )' % Afl)
xflp = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Afl), kflr, xflr, kflp,
            w.s([xflo, w.inst('simpl')], 'syl', '( %s -> k < x )' % Afl)], 'lttrd', '( %s -> 0 < x )' % Afl)
xflrp = w.s([xflr, xflp], 'elrpd', '( %s -> x e. RR+ )' % Afl)
kfl1r = w.s([kflr, w.s([r1], 'adantr', '( %s -> 1 e. RR )' % Afl)], 'readdcld', '( %s -> ( k + 1 ) e. RR )' % Afl)
kfl1p = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Afl), kflr, kfl1r, kflp,
             w.s([kflr], 'ltp1d', '( %s -> k < ( k + 1 ) )' % Afl)], 'lttrd', '( %s -> 0 < ( k + 1 ) )' % Afl)
kfl1rp = w.s([kfl1r, kfl1p], 'elrpd', '( %s -> ( k + 1 ) e. RR+ )' % Afl)
xle = w.s([xflr, kfl1r, w.s([xflo, w.inst('simpr')], 'syl', '( %s -> x < ( k + 1 ) )' % Afl)], 'ltled',
          '( %s -> x <_ ( k + 1 ) )' % Afl)
hL = w.s([w.s([xflrp, kfl1rp, w.s([tr], 'adantr', '( %s -> T e. RR )' % Afl)], '3jca',
               '( %s -> ( x e. RR+ /\\ ( k + 1 ) e. RR+ /\\ T e. RR ) )' % Afl),
          w.s([w.s([tge0b], 'adantr', '( %s -> 0 <_ T )' % Afl), xle], 'jca',
              '( %s -> ( 0 <_ T /\\ x <_ ( k + 1 ) ) )' % Afl), w.inst('cxpnegle')], 'syl2anc',
         '( %s -> ( ( k + 1 ) ^c -u T ) <_ ( x ^c -u T ) )' % Afl)
# the comparison
cmp = w.s([nu, hA, hVr, hB, hC, hD, hX, hL], 'dvfsumle',
          '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) <_ ( ( %s / ( 1 - T ) ) - ( %s / ( 1 - T ) ) ) )' % (A0, PN, PM))
# the arithmetic: ( PN / ( 1 - T ) ) - ( PM / ( 1 - T ) ) <_ ( PM / ( T - 1 ) )
pmrp = w.s([mrp, mtr], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, PM))
nrp = w.s([nr, w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), mr, nr, mpos,
                    w.s([nu, w.inst('eluzle')], 'syl', '( %s -> M <_ N )' % A0)], 'ltletrd', '( %s -> 0 < N )' % A0)],
           'elrpd', '( %s -> N e. RR+ )' % A0)
pnrp = w.s([nrp, mtr], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, PN))
pmc = w.s([pmrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, PM))
pnc = w.s([pnrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, PN))
dsd = w.s([pnc, pmc, mtc, mtne], 'divsubdird',
          '( %s -> ( ( %s - %s ) / ( 1 - T ) ) = ( ( %s / ( 1 - T ) ) - ( %s / ( 1 - T ) ) ) )' % (A0, PN, PM, PN, PM))
ng1 = w.s([pmc, pnc], 'negsubdi2d', '( %s -> -u ( %s - %s ) = ( %s - %s ) )' % (A0, PM, PN, PN, PM))
ng2 = w.s([tc, onec], 'negsubdi2d', '( %s -> -u ( T - 1 ) = ( 1 - T ) )' % A0)
d2n = w.s([w.s([pmc, pnc], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, PM, PN)),
           w.s([tm1rp], 'rpcnd', '( %s -> ( T - 1 ) e. CC )' % A0),
           w.s([tm1rp], 'rpne0d', '( %s -> ( T - 1 ) =/= 0 )' % A0)], 'div2negd',
          '( %s -> ( -u ( %s - %s ) / -u ( T - 1 ) ) = ( ( %s - %s ) / ( T - 1 ) ) )' % (A0, PM, PN, PM, PN))
e1 = w.s([ng1, ng2], 'oveq12d', '( %s -> ( -u ( %s - %s ) / -u ( T - 1 ) ) = ( ( %s - %s ) / ( 1 - T ) ) )' % (A0, PM, PN, PN, PM))
e2 = w.s([w.s([e1], 'eqcomd', '( %s -> ( ( %s - %s ) / ( 1 - T ) ) = ( -u ( %s - %s ) / -u ( T - 1 ) ) )' % (A0, PN, PM, PM, PN)), d2n],
         'eqtrd', '( %s -> ( ( %s - %s ) / ( 1 - T ) ) = ( ( %s - %s ) / ( T - 1 ) ) )' % (A0, PN, PM, PM, PN))
sble = w.s([w.s([pnrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, PN)),
            w.s([w.s([pnrp], 'rpred', '( %s -> %s e. RR )' % (A0, PN)), w.s([pmrp], 'rpred', '( %s -> %s e. RR )' % (A0, PM))],
                'subge02d', '( %s -> ( 0 <_ %s <-> ( %s - %s ) <_ %s ) )' % (A0, PN, PM, PN, PM))], 'mpbid',
           '( %s -> ( %s - %s ) <_ %s )' % (A0, PM, PN, PM))
divle = w.s([sble, w.s([w.s([w.s([pmrp], 'rpred', '( %s -> %s e. RR )' % (A0, PM)), w.s([pnrp], 'rpred', '( %s -> %s e. RR )' % (A0, PN))],
                            'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, PM, PN)),
                        w.s([pmrp], 'rpred', '( %s -> %s e. RR )' % (A0, PM)), tm1rp], 'lediv1d',
                       '( %s -> ( ( %s - %s ) <_ %s <-> ( ( %s - %s ) / ( T - 1 ) ) <_ ( %s / ( T - 1 ) ) ) )' % (A0, PM, PN, PM, PM, PN, PM))],
            'mpbid', '( %s -> ( ( %s - %s ) / ( T - 1 ) ) <_ ( %s / ( T - 1 ) ) )' % (A0, PM, PN, PM))
step = w.s([w.s([dsd], 'eqcomd', '( %s -> ( ( %s / ( 1 - T ) ) - ( %s / ( 1 - T ) ) ) = ( ( %s - %s ) / ( 1 - T ) ) )' % (A0, PN, PM, PN, PM)),
            e2], 'eqtrd', '( %s -> ( ( %s / ( 1 - T ) ) - ( %s / ( 1 - T ) ) ) = ( ( %s - %s ) / ( T - 1 ) ) )' % (A0, PN, PM, PM, PN))
fin = w.s([cmp, step], 'breqtrd',
          '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) <_ ( ( %s - %s ) / ( T - 1 ) ) )' % (A0, PM, PN))
sumre = w.s([w.s([w.s([], 'fzofi', '( M ..^ N ) e. Fin')], 'a1i', '( %s -> ( M ..^ N ) e. Fin )' % A0), hX],
            'fsumrecl', '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) e. RR )' % A0)
w.qed([sumre, fin, divle], 'letrd',
      '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) <_ ( %s / ( T - 1 ) ) )' % (A0, PM)); run3(w)

# ---- zserfz2 ---------------------------------------------------------------
w = W('zserfz2', 'The integral comparison for the zeta series, indexed by the summation variable itself.')
A0 = '( ( T e. RR /\\ 1 < T ) /\\ ( M e. NN /\\ N e. ( ZZ>= ` M ) ) )'
PM = '( M ^c ( 1 - T ) )'
FZ = '( ( M + 1 ) ... N )'
tt = w.s([], 'simpl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
mn = w.s([], 'simprl', '( %s -> M e. NN )' % A0)
nu = w.s([], 'simprr', '( %s -> N e. ( ZZ>= ` M ) )' % A0)
nz = w.s([nu, w.inst('eluzelz')], 'syl', '( %s -> N e. ZZ )' % A0)
mz = w.s([mn], 'nnzd', '( %s -> M e. ZZ )' % A0)
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A0)
n1z = w.s([nz, z1], 'zsubcld', '( %s -> ( N - 1 ) e. ZZ )' % A0)
base = w.s([], 'zserfz', '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) <_ ( %s / ( T - 1 ) ) )' % (A0, PM))
fzoe = w.s([nz, w.inst('fzoval')], 'syl', '( %s -> ( M ..^ N ) = ( M ... ( N - 1 ) ) )' % A0)
s1 = w.s([fzoe], 'sumeq1d',
         '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) = sum_ k e. ( M ... ( N - 1 ) ) ( ( k + 1 ) ^c -u T ) )' % A0)
cb = w.s([w.s([w.s([], 'oveq1', '( k = j -> ( k + 1 ) = ( j + 1 ) )')], 'oveq1d',
              '( k = j -> ( ( k + 1 ) ^c -u T ) = ( ( j + 1 ) ^c -u T ) )')], 'cbvsumv',
         'sum_ k e. ( M ... ( N - 1 ) ) ( ( k + 1 ) ^c -u T ) = sum_ j e. ( M ... ( N - 1 ) ) ( ( j + 1 ) ^c -u T )')
cbd = w.s([cb], 'a1i', '( %s -> sum_ k e. ( M ... ( N - 1 ) ) ( ( k + 1 ) ^c -u T ) = sum_ j e. ( M ... ( N - 1 ) ) ( ( j + 1 ) ^c -u T ) )' % A0)
Ajz = '( %s /\\ j e. ( M ... ( N - 1 ) ) )' % A0
jfz = w.s([], 'simpr', '( %s -> j e. ( M ... ( N - 1 ) ) )' % Ajz)
jz = w.s([jfz, w.inst('elfzelz')], 'syl', '( %s -> j e. ZZ )' % Ajz)
jc = w.s([jz], 'zcnd', '( %s -> j e. CC )' % Ajz)
j1c = w.s([jc, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % Ajz)], 'addcld',
          '( %s -> ( j + 1 ) e. CC )' % Ajz)
ntc = w.s([w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'negcld', '( %s -> -u T e. CC )' % A0)], 'adantr',
          '( %s -> -u T e. CC )' % Ajz)
jcl = w.s([j1c, ntc, w.inst('cxpcl')], 'syl2anc', '( %s -> ( ( j + 1 ) ^c -u T ) e. CC )' % Ajz)
sub = w.s([w.s([], 'oveq1', '( j = ( k - 1 ) -> ( j + 1 ) = ( ( k - 1 ) + 1 ) )')], 'oveq1d',
          '( j = ( k - 1 ) -> ( ( j + 1 ) ^c -u T ) = ( ( ( k - 1 ) + 1 ) ^c -u T ) )')
sh = w.s([z1, mz, n1z, jcl, sub], 'fsumshft',
         '( %s -> sum_ j e. ( M ... ( N - 1 ) ) ( ( j + 1 ) ^c -u T ) = sum_ k e. ( ( M + 1 ) ... ( ( N - 1 ) + 1 ) ) ( ( ( k - 1 ) + 1 ) ^c -u T ) )' % A0)
rng = w.s([w.s([nz], 'zcnd', '( %s -> N e. CC )' % A0), w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0)],
          'npcand', '( %s -> ( ( N - 1 ) + 1 ) = N )' % A0)
s2 = w.s([w.s([rng], 'oveq2d', '( %s -> ( ( M + 1 ) ... ( ( N - 1 ) + 1 ) ) = %s )' % (A0, FZ))], 'sumeq1d',
         '( %s -> sum_ k e. ( ( M + 1 ) ... ( ( N - 1 ) + 1 ) ) ( ( ( k - 1 ) + 1 ) ^c -u T ) = sum_ k e. %s ( ( ( k - 1 ) + 1 ) ^c -u T ) )' % (A0, FZ))
Akz = '( %s /\\ k e. %s )' % (A0, FZ)
kfz = w.s([], 'simpr', '( %s -> k e. %s )' % (Akz, FZ))
kz2 = w.s([kfz, w.inst('elfzelz')], 'syl', '( %s -> k e. ZZ )' % Akz)
kc2 = w.s([kz2], 'zcnd', '( %s -> k e. CC )' % Akz)
bd = w.s([w.s([kc2, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % Akz)], 'npcand',
              '( %s -> ( ( k - 1 ) + 1 ) = k )' % Akz)], 'oveq1d',
         '( %s -> ( ( ( k - 1 ) + 1 ) ^c -u T ) = ( k ^c -u T ) )' % Akz)
s3 = w.s([bd], 'sumeq2dv', '( %s -> sum_ k e. %s ( ( ( k - 1 ) + 1 ) ^c -u T ) = sum_ k e. %s ( k ^c -u T ) )' % (A0, FZ, FZ))
ch = w.s([w.s([w.s([s1, cbd], 'eqtrd', '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) = sum_ j e. ( M ... ( N - 1 ) ) ( ( j + 1 ) ^c -u T ) )' % A0),
               sh], 'eqtrd', '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) = sum_ k e. ( ( M + 1 ) ... ( ( N - 1 ) + 1 ) ) ( ( ( k - 1 ) + 1 ) ^c -u T ) )' % A0),
              w.s([s2, s3], 'eqtrd', '( %s -> sum_ k e. ( ( M + 1 ) ... ( ( N - 1 ) + 1 ) ) ( ( ( k - 1 ) + 1 ) ^c -u T ) = sum_ k e. %s ( k ^c -u T ) )' % (A0, FZ))],
         'eqtrd', '( %s -> sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) = sum_ k e. %s ( k ^c -u T ) )' % (A0, FZ))
w.qed([w.s([ch], 'eqcomd', '( %s -> sum_ k e. %s ( k ^c -u T ) = sum_ k e. ( M ..^ N ) ( ( k + 1 ) ^c -u T ) )' % (A0, FZ)), base],
      'eqbrtrd', '( %s -> sum_ k e. %s ( k ^c -u T ) <_ ( %s / ( T - 1 ) ) )' % (A0, FZ, PM)); run3(w)
