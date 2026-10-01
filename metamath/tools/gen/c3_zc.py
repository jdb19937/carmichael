"""Sortie C3 section 4: convergence of the zeta majorant and its tail bound."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

FN = '( n e. NN |-> ( n ^c -u T ) )'
PM = '( M ^c ( 1 - T ) )'
BND = '( %s / ( T - 1 ) )' % PM
UZ = '( ZZ>= ` ( M + 1 ) )'


def fnval(w, ante, var='k', dom='NN'):
    """( ( ante /\\ var e. dom ) -> ( FN ` var ) = ( var ^c -u T ) )"""
    A1 = '( %s /\\ %s e. %s )' % (ante, var, dom)
    e = w.s([], 'oveq1', '( n = %s -> ( n ^c -u T ) = ( %s ^c -u T ) )' % (var, var))
    em = w.s([], 'eqid', '%s = %s' % (FN, FN))
    fv = w.s([e, em], 'fvmptg',
             '( ( %s e. NN /\\ ( %s ^c -u T ) e. _V ) -> ( %s ` %s ) = ( %s ^c -u T ) )' % (var, var, FN, var, var))
    return fv


# ---- zsercvg ---------------------------------------------------------------
w = W('zsercvg', 'The zeta series converges for a real abscissa above one.')
A0 = '( T e. RR /\\ 1 < T )'
A1 = '( %s /\\ k e. NN )' % A0
tr = w.s([], 'simpl', '( %s -> T e. RR )' % A0)
t1 = w.s([], 'simpr', '( %s -> 1 < T )' % A0)
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
ret = w.s([tr, w.inst('rere')], 'syl', '( %s -> ( Re ` T ) = T )' % A0)
rgt = w.s([t1, w.s([ret], 'eqcomd', '( %s -> T = ( Re ` T ) )' % A0)], 'breqtrd', '( %s -> 1 < ( Re ` T ) )' % A0)
kn = w.s([], 'simpr', '( %s -> k e. NN )' % A1)
fv = fnval(w, A0)
vex = w.s([w.s([], 'ovex', '( k ^c -u T ) e. _V')], 'a1i', '( %s -> ( k ^c -u T ) e. _V )' % A1)
val = w.s([kn, vex, fv], 'syl2anc', '( %s -> ( %s ` k ) = ( k ^c -u T ) )' % (A1, FN))
w.qed([tc, rgt, val], 'zetacvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, FN)); run3(w)

# ---- zsertail --------------------------------------------------------------
w = W('zsertail', 'The tail of the zeta series is below the integral of its majorant.')
A0 = '( ( T e. RR /\\ 1 < T ) /\\ M e. NN )'
CST = '( %s X. { %s } )' % (UZ, BND)
SQ = 'seq ( M + 1 ) ( + , %s )' % FN
Ak = '( %s /\\ k e. %s )' % (A0, UZ)
Aj = '( %s /\\ j e. %s )' % (A0, UZ)
An = '( %s /\\ k e. NN )' % A0
Ajk = '( %s /\\ k e. ( ( M + 1 ) ... j ) )' % Aj
tt = w.s([], 'simpl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
t1a = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 1 < T )' % A0)
mn = w.s([], 'simpr', '( %s -> M e. NN )' % A0)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
ntr = w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)
m1n = w.s([mn, w.inst('peano2nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % A0)
m1z = w.s([m1n], 'nnzd', '( %s -> ( M + 1 ) e. ZZ )' % A0)
nu1 = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
u1n = w.s([nu1], 'eqcomi', '( ZZ>= ` 1 ) = NN')
m1u = w.s([m1n, w.s([u1n], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'eleqtrrd',
          '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
uss = w.s([w.s([m1u, w.inst('uzss')], 'syl', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (A0, UZ)),
           w.s([w.s([u1n], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'idi',
               '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'sseqtrd', '( %s -> %s C_ NN )' % (A0, UZ))
fvg = fnval(w, A0)


def vcl(ante, kmem, ntrs):
    """steps ( ante -> ( FN ` k ) = ( k ^c -u T ) ) and closures, given k e. NN step"""
    v = w.s([kmem, w.s([w.s([], 'ovex', '( k ^c -u T ) e. _V')], 'a1i', '( %s -> ( k ^c -u T ) e. _V )' % ante), fvg],
            'syl2anc', '( %s -> ( %s ` k ) = ( k ^c -u T ) )' % (ante, FN))
    rp = w.s([w.s([kmem], 'nnrpd', '( %s -> k e. RR+ )' % ante), ntrs], 'rpcxpcld',
             '( %s -> ( k ^c -u T ) e. RR+ )' % ante)
    return v, rp


# on NN
knnA = w.s([], 'simpr', '( %s -> k e. NN )' % An)
valn, nclA = vcl(An, knnA, w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % An))
nccc = w.s([valn, w.s([nclA], 'rpcnd', '( %s -> ( k ^c -u T ) e. CC )' % An)], 'eqeltrd',
           '( %s -> ( %s ` k ) e. CC )' % (An, FN))
# on the tail index set
knn = w.s([w.s([uss], 'adantr', '( %s -> %s C_ NN )' % (Ak, UZ)), w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, UZ))],
          'sseldd', '( %s -> k e. NN )' % Ak)
valu, kcl = vcl(Ak, knn, w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % Ak))
kcc = w.s([kcl], 'rpcnd', '( %s -> ( k ^c -u T ) e. CC )' % Ak)
# convergence
cv1 = w.s([tt, w.inst('zsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, FN))
exb = w.s([nu1, m1n, nccc], 'iserex', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> %s e. dom ~~> ) )' % (A0, FN, SQ))
cv2 = w.s([cv1, exb], 'mpbid', '( %s -> %s e. dom ~~> )' % (A0, SQ))
eqz = w.s([], 'eqid', '%s = %s' % (UZ, UZ))
lim = w.s([eqz, m1z, valu, kcc, cv2], 'isumclim2', '( %s -> %s ~~> sum_ k e. %s ( k ^c -u T ) )' % (A0, SQ, UZ))
# the bound as a constant sequence
pmrp = w.s([w.s([mn], 'nnrpd', '( %s -> M e. RR+ )' % A0), w.s([r1, tr], 'resubcld', '( %s -> ( 1 - T ) e. RR )' % A0)],
           'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, PM))
tm1 = w.s([tr, r1], 'resubcld', '( %s -> ( T - 1 ) e. RR )' % A0)
tm1rp = w.s([tm1, w.s([t1a, w.s([r1, tr], 'posdifd', '( %s -> ( 1 < T <-> 0 < ( T - 1 ) ) )' % A0)], 'mpbid',
                      '( %s -> 0 < ( T - 1 ) )' % A0)], 'elrpd', '( %s -> ( T - 1 ) e. RR+ )' % A0)
bndrp = w.s([pmrp, tm1rp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, BND))
bndre = w.s([bndrp], 'rpred', '( %s -> %s e. RR )' % (A0, BND))
bndcc = w.s([bndrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, BND))
cc2 = w.s([w.s([], 'ssid', '%s C_ %s' % (UZ, UZ)), w.s([], 'fvex', '%s e. _V' % UZ)], 'climconst2',
          '( ( %s e. CC /\\ ( M + 1 ) e. ZZ ) -> %s ~~> %s )' % (BND, CST, BND))
cst = w.s([bndcc, m1z, cc2], 'syl2anc', '( %s -> %s ~~> %s )' % (A0, CST, BND))
cstv = w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, UZ)), w.inst('fvconst2')], 'syl',
           '( %s -> ( %s ` k ) = %s )' % (Ak, CST, BND))
cstre = w.s([cstv, w.s([bndre], 'adantr', '( %s -> %s e. RR )' % (Ak, BND))], 'eqeltrd',
            '( %s -> ( %s ` k ) e. RR )' % (Ak, CST))
# the partial sums
jz = w.s([], 'simpr', '( %s -> j e. %s )' % (Aj, UZ))
kfzn = w.s([w.s([], 'simpr', '( %s -> k e. ( ( M + 1 ) ... j ) )' % Ajk), w.inst('elfzuz')], 'syl',
           '( %s -> k e. %s )' % (Ajk, UZ))
knnfz = w.s([w.s([w.s([uss], 'adantr', '( %s -> %s C_ NN )' % (Aj, UZ))], 'adantr', '( %s -> %s C_ NN )' % (Ajk, UZ)),
             kfzn], 'sseldd', '( %s -> k e. NN )' % Ajk)
valfz, clfz = vcl(Ajk, knnfz, w.s([w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % Aj)], 'adantr',
                                  '( %s -> -u T e. RR )' % Ajk))
clfzc = w.s([clfz], 'rpcnd', '( %s -> ( k ^c -u T ) e. CC )' % Ajk)
ser = w.s([valfz, jz, clfzc], 'fsumser', '( %s -> sum_ k e. ( ( M + 1 ) ... j ) ( k ^c -u T ) = ( %s ` j ) )' % (Aj, SQ))
serr = w.s([ser], 'eqcomd', '( %s -> ( %s ` j ) = sum_ k e. ( ( M + 1 ) ... j ) ( k ^c -u T ) )' % (Aj, SQ))
mzz = w.s([mn], 'nnzd', '( %s -> M e. ZZ )' % A0)
muz = w.s([mzz, w.inst('uzid')], 'syl', '( %s -> M e. ( ZZ>= ` M ) )' % A0)
m1uz = w.s([muz, w.inst('peano2uz')], 'syl', '( %s -> ( M + 1 ) e. ( ZZ>= ` M ) )' % A0)
ussm = w.s([m1uz, w.inst('uzss')], 'syl', '( %s -> %s C_ ( ZZ>= ` M ) )' % (A0, UZ))
juz = w.s([w.s([ussm], 'adantr', '( %s -> %s C_ ( ZZ>= ` M ) )' % (Aj, UZ)), jz], 'sseldd',
          '( %s -> j e. ( ZZ>= ` M ) )' % Aj)
zf2 = w.s([w.s([w.s([tt], 'adantr', '( %s -> ( T e. RR /\\ 1 < T ) )' % Aj),
                w.s([w.s([mn], 'adantr', '( %s -> M e. NN )' % Aj), juz], 'jca',
                    '( %s -> ( M e. NN /\\ j e. ( ZZ>= ` M ) ) )' % Aj)], 'jca',
               '( %s -> ( ( T e. RR /\\ 1 < T ) /\\ ( M e. NN /\\ j e. ( ZZ>= ` M ) ) ) )' % Aj), w.inst('zserfz2')],
          'syl', '( %s -> sum_ k e. ( ( M + 1 ) ... j ) ( k ^c -u T ) <_ %s )' % (Aj, BND))
pb = w.s([serr, zf2], 'eqbrtrd', '( %s -> ( %s ` j ) <_ %s )' % (Aj, SQ, BND))
cstvj = w.s([jz, w.inst('fvconst2')], 'syl', '( %s -> ( %s ` j ) = %s )' % (Aj, CST, BND))
pbj = w.s([pb, w.s([cstvj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (Aj, BND, CST))], 'breqtrd',
          '( %s -> ( %s ` j ) <_ ( %s ` j ) )' % (Aj, SQ, CST))
sqre = w.s([serr, w.s([w.s([], 'fzfid', '( %s -> ( ( M + 1 ) ... j ) e. Fin )' % Aj),
                       w.s([clfz], 'rpred', '( %s -> ( k ^c -u T ) e. RR )' % Ajk)], 'fsumrecl',
                      '( %s -> sum_ k e. ( ( M + 1 ) ... j ) ( k ^c -u T ) e. RR )' % Aj)], 'eqeltrd',
           '( %s -> ( %s ` j ) e. RR )' % (Aj, SQ))
cstrej = w.s([cstvj, w.s([bndre], 'adantr', '( %s -> %s e. RR )' % (Aj, BND))], 'eqeltrd',
             '( %s -> ( %s ` j ) e. RR )' % (Aj, CST))
w.qed([eqz, m1z, lim, cst, sqre, cstrej, pbj], 'climle',
      '( %s -> sum_ k e. %s ( k ^c -u T ) <_ %s )' % (A0, UZ, BND)); run3(w)

# ---- zserbnd ---------------------------------------------------------------
w = W('zserbnd', 'The zeta series is below one plus the reciprocal of the distance to the abscissa of convergence.')
A0 = '( T e. RR /\\ 1 < T )'
An = '( %s /\\ k e. NN )' % A0
U2 = '( ZZ>= ` ( 1 + 1 ) )'
tr = w.s([], 'simpl', '( %s -> T e. RR )' % A0)
t1 = w.s([], 'simpr', '( %s -> 1 < T )' % A0)
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
ntc = w.s([tc], 'negcld', '( %s -> -u T e. CC )' % A0)
ntr = w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
n1n = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0)
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A0)
nu1 = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
fvg = fnval(w, A0)
kn = w.s([], 'simpr', '( %s -> k e. NN )' % An)
valn = w.s([kn, w.s([w.s([], 'ovex', '( k ^c -u T ) e. _V')], 'a1i', '( %s -> ( k ^c -u T ) e. _V )' % An), fvg],
           'syl2anc', '( %s -> ( %s ` k ) = ( k ^c -u T ) )' % (An, FN))
kcl = w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % An), w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % An)],
          'rpcxpcld', '( %s -> ( k ^c -u T ) e. RR+ )' % An)
kcc = w.s([kcl], 'rpcnd', '( %s -> ( k ^c -u T ) e. CC )' % An)
cv = w.s([], 'zsercvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, FN))
sp = w.s([nu1, z1, valn, kcc, cv], 'isum1p',
         '( %s -> sum_ k e. NN ( k ^c -u T ) = ( ( %s ` 1 ) + sum_ k e. %s ( k ^c -u T ) ) )' % (A0, FN, U2))
# the first term is 1
e1 = w.s([], 'oveq1', '( n = 1 -> ( n ^c -u T ) = ( 1 ^c -u T ) )')
em = w.s([], 'eqid', '%s = %s' % (FN, FN))
fv1 = w.s([e1, em], 'fvmptg', '( ( 1 e. NN /\\ ( 1 ^c -u T ) e. _V ) -> ( %s ` 1 ) = ( 1 ^c -u T ) )' % FN)
v1 = w.s([n1n, w.s([w.s([], 'ovex', '( 1 ^c -u T ) e. _V')], 'a1i', '( %s -> ( 1 ^c -u T ) e. _V )' % A0), fv1],
         'syl2anc', '( %s -> ( %s ` 1 ) = ( 1 ^c -u T ) )' % (A0, FN))
c1 = w.s([ntc, w.inst('1cxp')], 'syl', '( %s -> ( 1 ^c -u T ) = 1 )' % A0)
first = w.s([v1, c1], 'eqtrd', '( %s -> ( %s ` 1 ) = 1 )' % (A0, FN))
# the tail
tail = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), n1n], 'jca',
                '( %s -> ( ( T e. RR /\\ 1 < T ) /\\ 1 e. NN ) )' % A0), w.inst('zsertail')], 'syl',
           '( %s -> sum_ k e. %s ( k ^c -u T ) <_ ( ( 1 ^c ( 1 - T ) ) / ( T - 1 ) ) )' % (A0, U2))
mtc = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0), tc], 'subcld',
          '( %s -> ( 1 - T ) e. CC )' % A0)
c1b = w.s([mtc, w.inst('1cxp')], 'syl', '( %s -> ( 1 ^c ( 1 - T ) ) = 1 )' % A0)
tail2 = w.s([tail, w.s([c1b], 'oveq1d', '( %s -> ( ( 1 ^c ( 1 - T ) ) / ( T - 1 ) ) = ( 1 / ( T - 1 ) ) )' % A0)],
            'breqtrd', '( %s -> sum_ k e. %s ( k ^c -u T ) <_ ( 1 / ( T - 1 ) ) )' % (A0, U2))
# the closures for the final inequality
tm1 = w.s([tr, r1], 'resubcld', '( %s -> ( T - 1 ) e. RR )' % A0)
tm1rp = w.s([tm1, w.s([t1, w.s([r1, tr], 'posdifd', '( %s -> ( 1 < T <-> 0 < ( T - 1 ) ) )' % A0)], 'mpbid',
                      '( %s -> 0 < ( T - 1 ) )' % A0)], 'elrpd', '( %s -> ( T - 1 ) e. RR+ )' % A0)
recre = w.s([w.s([tm1rp], 'rpreccld', '( %s -> ( 1 / ( T - 1 ) ) e. RR+ )' % A0)], 'rpred',
            '( %s -> ( 1 / ( T - 1 ) ) e. RR )' % A0)
# the tail sum is real: it is bounded above and the series converges
m1n = w.s([n1n, w.inst('peano2nn')], 'syl', '( %s -> ( 1 + 1 ) e. NN )' % A0)
u2ss = w.s([w.s([w.s([m1n, w.s([w.s([nu1], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i',
                               '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'eleqtrrd', '( %s -> ( 1 + 1 ) e. ( ZZ>= ` 1 ) )' % A0),
                w.inst('uzss')], 'syl', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (A0, U2)),
               w.s([w.s([w.s([nu1], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)],
                   'idi', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'sseqtrd', '( %s -> %s C_ NN )' % (A0, U2))
A2 = '( %s /\\ k e. %s )' % (A0, U2)
knn2 = w.s([w.s([u2ss], 'adantr', '( %s -> %s C_ NN )' % (A2, U2)), w.s([], 'simpr', '( %s -> k e. %s )' % (A2, U2))],
           'sseldd', '( %s -> k e. NN )' % A2)
val2 = w.s([knn2, w.s([w.s([], 'ovex', '( k ^c -u T ) e. _V')], 'a1i', '( %s -> ( k ^c -u T ) e. _V )' % A2), fvg],
           'syl2anc', '( %s -> ( %s ` k ) = ( k ^c -u T ) )' % (A2, FN))
cl2 = w.s([w.s([knn2], 'nnrpd', '( %s -> k e. RR+ )' % A2), w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % A2)],
          'rpcxpcld', '( %s -> ( k ^c -u T ) e. RR+ )' % A2)
cvb = w.s([nu1, m1n, w.s([valn, kcc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (An, FN))], 'iserex',
          '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( 1 + 1 ) ( + , %s ) e. dom ~~> ) )' % (A0, FN, FN))
cv2 = w.s([cv, cvb], 'mpbid', '( %s -> seq ( 1 + 1 ) ( + , %s ) e. dom ~~> )' % (A0, FN))
eq2 = w.s([], 'eqid', '%s = %s' % (U2, U2))
m1zz = w.s([m1n], 'nnzd', '( %s -> ( 1 + 1 ) e. ZZ )' % A0)
tlre = w.s([eq2, m1zz, val2, w.s([cl2], 'rpred', '( %s -> ( k ^c -u T ) e. RR )' % A2), cv2], 'isumrecl',
           '( %s -> sum_ k e. %s ( k ^c -u T ) e. RR )' % (A0, U2))
add = w.s([tlre, recre, r1, tail2], 'leadd2dd',
          '( %s -> ( 1 + sum_ k e. %s ( k ^c -u T ) ) <_ ( 1 + ( 1 / ( T - 1 ) ) ) )' % (A0, U2))
seq = w.s([sp, w.s([first], 'oveq1d', '( %s -> ( ( %s ` 1 ) + sum_ k e. %s ( k ^c -u T ) ) = ( 1 + sum_ k e. %s ( k ^c -u T ) ) )' % (A0, FN, U2, U2))],
          'eqtrd', '( %s -> sum_ k e. NN ( k ^c -u T ) = ( 1 + sum_ k e. %s ( k ^c -u T ) ) )' % (A0, U2))
w.qed([seq, add], 'eqbrtrd', '( %s -> sum_ k e. NN ( k ^c -u T ) <_ ( 1 + ( 1 / ( T - 1 ) ) ) )' % A0); run3(w)
