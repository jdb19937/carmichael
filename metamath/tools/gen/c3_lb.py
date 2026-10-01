"""Sortie C3 section 7: the lower bound for the L-series of a character on Re s >= 2."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from lin import linarith

GG = '( DChr ` N )'; ZN = '( Z/nZ ` N )'; LH = '( ZRHom ` %s )' % ZN; DC = '( Base ` %s )' % GG
AX = '( q e. NN |-> ( X ` ( %s ` q ) ) )' % LH
RZ = '( Re ` Z )'
GN = '( n e. NN |-> ( ( %s ` n ) x. ( n ^c -u Z ) ) )' % AX
TWO = '( 1 + 1 )'
U2 = '( ZZ>= ` %s )' % TWO
U3 = '( ZZ>= ` ( %s + 1 ) )' % TWO
TRMK = '( ( %s ` k ) x. ( k ^c -u Z ) )' % AX
XTRMK = '( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) )' % LH
CFBX = '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (AX, AX)


def dchyp(w):
    return [w.s([], 'eqid', '%s = %s' % (GG, GG)), w.s([], 'eqid', '%s = %s' % (ZN, ZN)),
            w.s([], 'eqid', '%s = %s' % (DC, DC)), w.s([], 'eqid', '%s = %s' % (LH, LH))]


# ---- cxp2le ----------------------------------------------------------------
w = W('cxp2le', 'Two to a negative power below minus one is at most one half; below minus two, at most one quarter.')
A0 = '( ( T e. RR /\\ U e. RR ) /\\ T <_ U )'
tr = w.s([], 'simpll', '( %s -> T e. RR )' % A0)
ur = w.s([], 'simplr', '( %s -> U e. RR )' % A0)
le = w.s([], 'simpr', '( %s -> T <_ U )' % A0)
r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
g2 = w.s([w.s([], '1lt2', '1 < 2')], 'a1i', '( %s -> 1 < 2 )' % A0)
le2 = w.s([r2, g2, tr, ur], 'cxpled', '( %s -> ( T <_ U <-> ( 2 ^c T ) <_ ( 2 ^c U ) ) )' % A0)
w.qed([le, le2], 'mpbid', '( %s -> ( 2 ^c T ) <_ ( 2 ^c U ) )' % A0); run3(w)

# ---- lchrlb ----------------------------------------------------------------
w = W('lchrlb', 'The Dirichlet L-series of a character is bounded below by one quarter on the half-plane to the right of the line two.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ ( Z e. CC /\\ 2 <_ %s ) )' % (DC, RZ)
Ak = '( %s /\\ k e. NN )' % A0
Au = '( %s /\\ k e. %s )' % (A0, U2)
g, z, b, l = dchyp(w)
nx = w.s([], 'simpl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))
nn = w.s([nx, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
xd = w.s([nx, w.inst('simpr')], 'syl', '( %s -> X e. %s )' % (A0, DC))
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
z2 = w.s([], 'simprr', '( %s -> 2 <_ %s )' % (A0, RZ))
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
gt1 = linarith(w, A0, [z2], '1 < %s' % RZ, leaves={RZ: rz})
cfbx = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX))
dsh = w.s([cfbx, w.s([zc, gt1], 'jca', '( %s -> ( Z e. CC /\\ 1 < %s ) )' % (A0, RZ))], 'jca',
          '( %s -> ( %s /\\ ( Z e. CC /\\ 1 < %s ) ) )' % (A0, CFBX, RZ))
cvg = w.s([dsh, w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GN))
# the termwise values and closures on NN
nu1 = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A0)
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
subg = w.s([w.s([], 'fveq2', '( n = k -> ( %s ` n ) = ( %s ` k ) )' % (AX, AX)),
            w.s([], 'oveq1', '( n = k -> ( n ^c -u Z ) = ( k ^c -u Z ) )')], 'oveq12d',
           '( n = k -> ( ( %s ` n ) x. ( n ^c -u Z ) ) = %s )' % (AX, TRMK))
vG = mpv(w, Ak, GN, 'k', TRMK, subg, kn, vexd(w, Ak, TRMK))
axk = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ak, DC)), kn], 'jca',
                '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Ak, DC)), w.inst('lchrval')], 'syl',
           '( %s -> ( %s ` k ) = ( X ` ( %s ` k ) ) )' % (Ak, AX, LH))
axcc = w.s([axk, w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ak, DC)), kn], 'jca',
                          '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Ak, DC)), w.inst('lchrcl')], 'syl',
                     '( %s -> ( X ` ( %s ` k ) ) e. CC )' % (Ak, LH))], 'eqeltrd',
           '( %s -> ( %s ` k ) e. CC )' % (Ak, AX))
pk = w.s([w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)], 'rpcnd', '( %s -> k e. CC )' % Ak),
          w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)], 'negcld', '( %s -> -u Z e. CC )' % Ak),
          w.inst('cxpcl')], 'syl2anc', '( %s -> ( k ^c -u Z ) e. CC )' % Ak)
trmc = w.s([axcc, pk], 'mulcld', '( %s -> %s e. CC )' % (Ak, TRMK))
# peel the first term
sp1 = w.s([nu1, z1, vG, trmc, cvg], 'isum1p',
          '( %s -> sum_ k e. NN %s = ( ( %s ` 1 ) + sum_ k e. %s %s ) )' % (A0, TRMK, GN, U2, TRMK))
n1n = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0)
sub1 = w.s([w.s([], 'fveq2', '( n = 1 -> ( %s ` n ) = ( %s ` 1 ) )' % (AX, AX)),
            w.s([], 'oveq1', '( n = 1 -> ( n ^c -u Z ) = ( 1 ^c -u Z ) )')], 'oveq12d',
           '( n = 1 -> ( ( %s ` n ) x. ( n ^c -u Z ) ) = ( ( %s ` 1 ) x. ( 1 ^c -u Z ) ) )' % (AX, AX))
vG1 = mpv(w, A0, GN, '1', '( ( %s ` 1 ) x. ( 1 ^c -u Z ) )' % AX, sub1, n1n,
          vexd(w, A0, '( ( %s ` 1 ) x. ( 1 ^c -u Z ) )' % AX))
ax1 = w.s([w.s([nx, n1n], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ 1 e. NN ) )' % (A0, DC)), w.inst('lchrval')],
          'syl', '( %s -> ( %s ` 1 ) = ( X ` ( %s ` 1 ) ) )' % (A0, AX, LH))
chi1 = w.s([g, z, b, l, xd], 'dchrzrh1', '( %s -> ( X ` ( %s ` 1 ) ) = 1 )' % (A0, LH))
one1 = w.s([w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('1cxp')], 'syl',
           '( %s -> ( 1 ^c -u Z ) = 1 )' % A0)
first = w.s([vG1, w.s([w.s([ax1, chi1], 'eqtrd', '( %s -> ( %s ` 1 ) = 1 )' % (A0, AX)), one1], 'oveq12d',
                      '( %s -> ( ( %s ` 1 ) x. ( 1 ^c -u Z ) ) = ( 1 x. 1 ) )' % (A0, AX))], 'eqtrd',
            '( %s -> ( %s ` 1 ) = ( 1 x. 1 ) )' % (A0, GN))
first2 = w.s([first, w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % A0)], 'eqtrd',
             '( %s -> ( %s ` 1 ) = 1 )' % (A0, GN))
# peel the second term
twon = w.s([n1n, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (A0, TWO))
twoz = w.s([twon], 'nnzd', '( %s -> %s e. ZZ )' % (A0, TWO))
gcc = w.s([vG, trmc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, GN))
u1n = w.s([w.s([nu1], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)
twou = w.s([twon, u1n], 'eleqtrrd', '( %s -> %s e. ( ZZ>= ` 1 ) )' % (A0, TWO))
uss = w.s([w.s([twou, w.inst('uzss')], 'syl', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (A0, U2)), u1n], 'sseqtrd',
          '( %s -> %s C_ NN )' % (A0, U2))
cvg2 = w.s([cvg, w.s([nu1, twon, gcc], 'iserex',
                     '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq %s ( + , %s ) e. dom ~~> ) )' % (A0, GN, TWO, GN))],
           'mpbid', '( %s -> seq %s ( + , %s ) e. dom ~~> )' % (A0, TWO, GN))
knu = w.s([w.s([uss], 'adantr', '( %s -> %s C_ NN )' % (Au, U2)), w.s([], 'simpr', '( %s -> k e. %s )' % (Au, U2))],
          'sseldd', '( %s -> k e. NN )' % Au)
vGu = mpv(w, Au, GN, 'k', TRMK, subg, knu, vexd(w, Au, TRMK))
axku = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Au, DC)), knu], 'jca',
                 '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Au, DC)), w.inst('lchrcl')], 'syl',
           '( %s -> ( X ` ( %s ` k ) ) e. CC )' % (Au, LH))
axvu = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Au, DC)), knu], 'jca',
                 '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Au, DC)), w.inst('lchrval')], 'syl',
           '( %s -> ( %s ` k ) = ( X ` ( %s ` k ) ) )' % (Au, AX, LH))
axccu = w.s([axvu, axku], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Au, AX))
pku = w.s([w.s([w.s([knu], 'nnrpd', '( %s -> k e. RR+ )' % Au)], 'rpcnd', '( %s -> k e. CC )' % Au),
           w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Au)], 'negcld', '( %s -> -u Z e. CC )' % Au),
           w.inst('cxpcl')], 'syl2anc', '( %s -> ( k ^c -u Z ) e. CC )' % Au)
trmcu = w.s([axccu, pku], 'mulcld', '( %s -> %s e. CC )' % (Au, TRMK))
equ2 = w.s([], 'eqid', '%s = ( ZZ>= ` %s )' % (U2, TWO))
sp2 = w.s([equ2, twoz, vGu, trmcu, cvg2], 'isum1p',
          '( %s -> sum_ k e. %s %s = ( ( %s ` %s ) + sum_ k e. %s %s ) )' % (A0, U2, TRMK, GN, TWO, U3, TRMK))
# the modulus of the second term
sub2 = w.s([w.s([], 'fveq2', '( n = %s -> ( %s ` n ) = ( %s ` %s ) )' % (TWO, AX, AX, TWO)),
            w.s([], 'oveq1', '( n = %s -> ( n ^c -u Z ) = ( %s ^c -u Z ) )' % (TWO, TWO))], 'oveq12d',
           '( n = %s -> ( ( %s ` n ) x. ( n ^c -u Z ) ) = ( ( %s ` %s ) x. ( %s ^c -u Z ) ) )' % (TWO, AX, AX, TWO, TWO))
vG2 = mpv(w, A0, GN, TWO, '( ( %s ` %s ) x. ( %s ^c -u Z ) )' % (AX, TWO, TWO), sub2, twon,
          vexd(w, A0, '( ( %s ` %s ) x. ( %s ^c -u Z ) )' % (AX, TWO, TWO)))
dtm2 = w.s([w.s([cfbx, w.s([w.s([twon, rz, zc], '3jca', '( %s -> ( %s e. NN /\\ %s e. RR /\\ Z e. CC ) )' % (A0, TWO, RZ)),
                            w.s([rz], 'leidd', '( %s -> %s <_ %s )' % (A0, RZ, RZ))], 'jca',
                           '( %s -> ( ( %s e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) )' % (A0, TWO, RZ, RZ, RZ))], 'jca',
                '( %s -> ( %s /\\ ( ( %s e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) ) )' % (A0, CFBX, TWO, RZ, RZ, RZ)),
            w.inst('dtmabs')], 'syl',
           '( %s -> ( abs ` ( ( %s ` %s ) x. ( %s ^c -u Z ) ) ) <_ ( 1 x. ( %s ^c -u %s ) ) )' % (A0, AX, TWO, TWO, TWO, RZ))
# ( 1 + 1 ) = 2 and the numeral bounds
axtwo0 = w.s([w.s([nx, twon], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ %s e. NN ) )' % (A0, DC, TWO)),
              w.inst('lchrval')], 'syl', '( %s -> ( %s ` %s ) = ( X ` ( %s ` %s ) ) )' % (A0, AX, TWO, LH, TWO))
cltwo0 = w.s([w.s([nx, twon], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ %s e. NN ) )' % (A0, DC, TWO)),
              w.inst('lchrcl')], 'syl', '( %s -> ( X ` ( %s ` %s ) ) e. CC )' % (A0, LH, TWO))
axtwoc0 = w.s([axtwo0, cltwo0], 'eqeltrd', '( %s -> ( %s ` %s ) e. CC )' % (A0, AX, TWO))
ptwo0 = w.s([w.s([w.s([twon], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, TWO))], 'rpcnd', '( %s -> %s e. CC )' % (A0, TWO)),
             w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')], 'syl2anc',
            '( %s -> ( %s ^c -u Z ) e. CC )' % (A0, TWO))
t2 = w.s([w.s([], '1p1e2', '%s = 2' % TWO)], 'a1i', '( %s -> %s = 2 )' % (A0, TWO))
nrz = w.s([rz], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))
nr2 = w.s([r2], 'renegcld', '( %s -> -u 2 e. RR )' % A0)
nle = linarith(w, A0, [z2], '-u %s <_ -u 2' % RZ, leaves={RZ: rz})
c2a = w.s([w.s([w.s([nrz, nr2], 'jca', '( %s -> ( -u %s e. RR /\\ -u 2 e. RR ) )' % (A0, RZ)), nle], 'jca',
                '( %s -> ( ( -u %s e. RR /\\ -u 2 e. RR ) /\\ -u %s <_ -u 2 ) )' % (A0, RZ, RZ)), w.inst('cxp2le')],
          'syl', '( %s -> ( 2 ^c -u %s ) <_ ( 2 ^c -u 2 ) )' % (A0, RZ))
# 2 ^c -u 2 = 1 / 4
c2c = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0)
c2n = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % A0)
e1 = w.s([c2c, c2n, c2c, w.inst('cxpneg')], 'syl3anc', '( %s -> ( 2 ^c -u 2 ) = ( 1 / ( 2 ^c 2 ) ) )' % A0)
e2 = w.s([c2c, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A0), w.inst('cxpexp')], 'syl2anc',
         '( %s -> ( 2 ^c 2 ) = ( 2 ^ 2 ) )' % A0)
e3 = w.s([w.s([e2, w.s([w.s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '( %s -> ( 2 ^ 2 ) = 4 )' % A0)], 'eqtrd',
               '( %s -> ( 2 ^c 2 ) = 4 )' % A0)], 'oveq2d', '( %s -> ( 1 / ( 2 ^c 2 ) ) = ( 1 / 4 ) )' % A0)
c2q = w.s([e1, e3], 'eqtrd', '( %s -> ( 2 ^c -u 2 ) = ( 1 / 4 ) )' % A0)
tw2 = w.s([w.s([t2], 'oveq1d', '( %s -> ( %s ^c -u %s ) = ( 2 ^c -u %s ) )' % (A0, TWO, RZ, RZ))], 'idi',
          '( %s -> ( %s ^c -u %s ) = ( 2 ^c -u %s ) )' % (A0, TWO, RZ, RZ))
b2a = w.s([w.s([tw2, c2a], 'eqbrtrd', '( %s -> ( %s ^c -u %s ) <_ ( 2 ^c -u 2 ) )' % (A0, TWO, RZ)), c2q], 'breqtrd',
          '( %s -> ( %s ^c -u %s ) <_ ( 1 / 4 ) )' % (A0, TWO, RZ))
twrp = w.s([twon], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, TWO))
pw2 = w.s([w.s([twrp, nrz], 'rpcxpcld', '( %s -> ( %s ^c -u %s ) e. RR+ )' % (A0, TWO, RZ))], 'rpred',
          '( %s -> ( %s ^c -u %s ) e. RR )' % (A0, TWO, RZ))
mul1 = w.s([w.s([pw2], 'recnd', '( %s -> ( %s ^c -u %s ) e. CC )' % (A0, TWO, RZ)), w.inst('mullid')], 'syl',
           '( %s -> ( 1 x. ( %s ^c -u %s ) ) = ( %s ^c -u %s ) )' % (A0, TWO, RZ, TWO, RZ))
r4 = w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % A0)
q4 = w.s([r1, r4, w.s([w.s([], '4ne0', '4 =/= 0')], 'a1i', '( %s -> 4 =/= 0 )' % A0)], 'redivcld',
         '( %s -> ( 1 / 4 ) e. RR )' % A0)
t2p = w.s([axtwoc0, ptwo0], 'mulcld', '( %s -> ( ( %s ` %s ) x. ( %s ^c -u Z ) ) e. CC )' % (A0, AX, TWO, TWO))
t2r = w.s([t2p], 'abscld', '( %s -> ( abs ` ( ( %s ` %s ) x. ( %s ^c -u Z ) ) ) e. RR )' % (A0, AX, TWO, TWO))
t2abs = w.s([t2r, pw2, q4,
             w.s([dtm2, mul1], 'breqtrd',
                 '( %s -> ( abs ` ( ( %s ` %s ) x. ( %s ^c -u Z ) ) ) <_ ( %s ^c -u %s ) )' % (A0, AX, TWO, TWO, TWO, RZ)),
             b2a], 'letrd', '( %s -> ( abs ` ( ( %s ` %s ) x. ( %s ^c -u Z ) ) ) <_ ( 1 / 4 ) )' % (A0, AX, TWO, TWO))
t2b = w.s([w.s([vG2], 'fveq2d', '( %s -> ( abs ` ( %s ` %s ) ) = ( abs ` ( ( %s ` %s ) x. ( %s ^c -u Z ) ) ) )' % (A0, GN, TWO, AX, TWO, TWO)),
           t2abs], 'eqbrtrd', '( %s -> ( abs ` ( %s ` %s ) ) <_ ( 1 / 4 ) )' % (A0, GN, TWO))
# the tail from ( ZZ>= ` ( ( 1 + 1 ) + 1 ) )
tl = w.s([w.s([dsh, twon], 'jca', '( %s -> ( ( %s /\\ ( Z e. CC /\\ 1 < %s ) ) /\\ %s e. NN ) )' % (A0, CFBX, RZ, TWO)),
          w.inst('dsertl')], 'syl',
         '( %s -> ( abs ` sum_ k e. %s %s ) <_ ( 1 x. ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) ) )' % (A0, U3, TRMK, TWO, RZ, RZ))
mtr = w.s([r1, rz], 'resubcld', '( %s -> ( 1 - %s ) e. RR )' % (A0, RZ))
nrr = w.s([r1], 'renegcld', '( %s -> -u 1 e. RR )' % A0)
mle = linarith(w, A0, [z2], '( 1 - %s ) <_ -u 1' % RZ, leaves={RZ: rz})
c2b = w.s([w.s([w.s([mtr, nrr], 'jca', '( %s -> ( ( 1 - %s ) e. RR /\\ -u 1 e. RR ) )' % (A0, RZ)), mle], 'jca',
                '( %s -> ( ( ( 1 - %s ) e. RR /\\ -u 1 e. RR ) /\\ ( 1 - %s ) <_ -u 1 ) )' % (A0, RZ, RZ)),
           w.inst('cxp2le')], 'syl', '( %s -> ( 2 ^c ( 1 - %s ) ) <_ ( 2 ^c -u 1 ) )' % (A0, RZ))
h1 = w.s([c2c, c2n, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0), w.inst('cxpneg')], 'syl3anc',
         '( %s -> ( 2 ^c -u 1 ) = ( 1 / ( 2 ^c 1 ) ) )' % A0)
h2 = w.s([w.s([w.s([c2c, w.inst('cxp1')], 'syl', '( %s -> ( 2 ^c 1 ) = 2 )' % A0)], 'oveq2d',
               '( %s -> ( 1 / ( 2 ^c 1 ) ) = ( 1 / 2 ) )' % A0)], 'idi', '( %s -> ( 1 / ( 2 ^c 1 ) ) = ( 1 / 2 ) )' % A0)
c2h = w.s([h1, h2], 'eqtrd', '( %s -> ( 2 ^c -u 1 ) = ( 1 / 2 ) )' % A0)
twm = w.s([w.s([t2], 'oveq1d', '( %s -> ( %s ^c ( 1 - %s ) ) = ( 2 ^c ( 1 - %s ) ) )' % (A0, TWO, RZ, RZ))], 'idi',
          '( %s -> ( %s ^c ( 1 - %s ) ) = ( 2 ^c ( 1 - %s ) ) )' % (A0, TWO, RZ, RZ))
numle = w.s([w.s([twm, c2b], 'eqbrtrd', '( %s -> ( %s ^c ( 1 - %s ) ) <_ ( 2 ^c -u 1 ) )' % (A0, TWO, RZ)), c2h],
            'breqtrd', '( %s -> ( %s ^c ( 1 - %s ) ) <_ ( 1 / 2 ) )' % (A0, TWO, RZ))
tm1rp = w.s([w.s([rz, r1], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (A0, RZ)),
             linarith(w, A0, [z2], '0 < ( %s - 1 )' % RZ, leaves={RZ: rz})], 'elrpd',
            '( %s -> ( %s - 1 ) e. RR+ )' % (A0, RZ))
pwm = w.s([w.s([twrp, mtr], 'rpcxpcld', '( %s -> ( %s ^c ( 1 - %s ) ) e. RR+ )' % (A0, TWO, RZ))], 'rpred',
          '( %s -> ( %s ^c ( 1 - %s ) ) e. RR )' % (A0, TWO, RZ))
hre = w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % A0)
d1 = w.s([numle, w.s([pwm, hre, tm1rp], 'lediv1d',
                     '( %s -> ( ( %s ^c ( 1 - %s ) ) <_ ( 1 / 2 ) <-> ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) <_ ( ( 1 / 2 ) / ( %s - 1 ) ) ) )' % (A0, TWO, RZ, TWO, RZ, RZ, RZ))],
         'mpbid', '( %s -> ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) <_ ( ( 1 / 2 ) / ( %s - 1 ) ) )' % (A0, TWO, RZ, RZ, RZ))
d2 = w.s([w.s([w.s([r1, w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % A0)], 'jca',
                    '( %s -> ( 1 e. RR /\\ 0 < 1 ) )' % A0),
               w.s([w.s([tm1rp], 'rpred', '( %s -> ( %s - 1 ) e. RR )' % (A0, RZ)),
                    w.s([tm1rp], 'rpgt0d', '( %s -> 0 < ( %s - 1 ) )' % (A0, RZ))], 'jca',
                   '( %s -> ( ( %s - 1 ) e. RR /\\ 0 < ( %s - 1 ) ) )' % (A0, RZ, RZ)),
               w.s([hre, w.s([w.s([], 'halfge0', '0 <_ ( 1 / 2 )')], 'a1i', '( %s -> 0 <_ ( 1 / 2 ) )' % A0)], 'jca',
                   '( %s -> ( ( 1 / 2 ) e. RR /\\ 0 <_ ( 1 / 2 ) ) )' % A0)], '3jca',
              '( %s -> ( ( 1 e. RR /\\ 0 < 1 ) /\\ ( ( %s - 1 ) e. RR /\\ 0 < ( %s - 1 ) ) /\\ ( ( 1 / 2 ) e. RR /\\ 0 <_ ( 1 / 2 ) ) ) )' % (A0, RZ, RZ)),
          linarith(w, A0, [z2], '1 <_ ( %s - 1 )' % RZ, leaves={RZ: rz}), w.inst('lediv2a')], 'syl2anc',
         '( %s -> ( ( 1 / 2 ) / ( %s - 1 ) ) <_ ( ( 1 / 2 ) / 1 ) )' % (A0, RZ))
d3 = w.s([d2, w.s([w.s([w.s([hre], 'recnd', '( %s -> ( 1 / 2 ) e. CC )' % A0), w.inst('div1')], 'syl',
                        '( %s -> ( ( 1 / 2 ) / 1 ) = ( 1 / 2 ) )' % A0)], 'idi', '( %s -> ( ( 1 / 2 ) / 1 ) = ( 1 / 2 ) )' % A0)],
         'breqtrd', '( %s -> ( ( 1 / 2 ) / ( %s - 1 ) ) <_ ( 1 / 2 ) )' % (A0, RZ))
qre = w.s([w.s([w.s([twrp, mtr], 'rpcxpcld', '( %s -> ( %s ^c ( 1 - %s ) ) e. RR+ )' % (A0, TWO, RZ)), tm1rp], 'rpdivcld',
                '( %s -> ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) e. RR+ )' % (A0, TWO, RZ, RZ))], 'rpred',
          '( %s -> ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) e. RR )' % (A0, TWO, RZ, RZ))
hdre = w.s([hre, w.s([tm1rp], 'rpred', '( %s -> ( %s - 1 ) e. RR )' % (A0, RZ)),
            w.s([tm1rp], 'rpne0d', '( %s -> ( %s - 1 ) =/= 0 )' % (A0, RZ))], 'redivcld',
           '( %s -> ( ( 1 / 2 ) / ( %s - 1 ) ) e. RR )' % (A0, RZ))
qle = w.s([qre, hdre, hre, d1, d3], 'letrd',
          '( %s -> ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) <_ ( 1 / 2 ) )' % (A0, TWO, RZ, RZ))
mulq = w.s([w.s([qre], 'recnd', '( %s -> ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) e. CC )' % (A0, TWO, RZ, RZ)),
            w.inst('mullid')], 'syl',
           '( %s -> ( 1 x. ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) ) = ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) )' % (A0, TWO, RZ, RZ, TWO, RZ, RZ))
tlcl = w.s([equ2, twoz, vGu, trmcu, cvg2], 'isumcl', '( %s -> sum_ k e. %s %s e. CC )' % (A0, U2, TRMK))
# the tail sum is a complex number
Av = '( %s /\\ k e. %s )' % (A0, U3)
tw1n = w.s([twon, w.inst('peano2nn')], 'syl', '( %s -> ( %s + 1 ) e. NN )' % (A0, TWO))
tw1z = w.s([tw1n], 'nnzd', '( %s -> ( %s + 1 ) e. ZZ )' % (A0, TWO))
tw1u = w.s([tw1n, u1n], 'eleqtrrd', '( %s -> ( %s + 1 ) e. ( ZZ>= ` 1 ) )' % (A0, TWO))
uss3 = w.s([w.s([tw1u, w.inst('uzss')], 'syl', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (A0, U3)), u1n], 'sseqtrd',
           '( %s -> %s C_ NN )' % (A0, U3))
knv = w.s([w.s([uss3], 'adantr', '( %s -> %s C_ NN )' % (Av, U3)), w.s([], 'simpr', '( %s -> k e. %s )' % (Av, U3))],
          'sseldd', '( %s -> k e. NN )' % Av)
vGv = mpv(w, Av, GN, 'k', TRMK, subg, knv, vexd(w, Av, TRMK))
axkv = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Av, DC)), knv], 'jca',
                 '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Av, DC)), w.inst('lchrcl')], 'syl',
           '( %s -> ( X ` ( %s ` k ) ) e. CC )' % (Av, LH))
axvv = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Av, DC)), knv], 'jca',
                 '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Av, DC)), w.inst('lchrval')], 'syl',
           '( %s -> ( %s ` k ) = ( X ` ( %s ` k ) ) )' % (Av, AX, LH))
pkv = w.s([w.s([w.s([knv], 'nnrpd', '( %s -> k e. RR+ )' % Av)], 'rpcnd', '( %s -> k e. CC )' % Av),
           w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Av)], 'negcld', '( %s -> -u Z e. CC )' % Av),
           w.inst('cxpcl')], 'syl2anc', '( %s -> ( k ^c -u Z ) e. CC )' % Av)
trmcv = w.s([w.s([axvv, axkv], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Av, AX)), pkv], 'mulcld',
            '( %s -> %s e. CC )' % (Av, TRMK))
cvg3 = w.s([cvg, w.s([nu1, tw1n, gcc], 'iserex',
                     '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( %s + 1 ) ( + , %s ) e. dom ~~> ) )' % (A0, GN, TWO, GN))],
           'mpbid', '( %s -> seq ( %s + 1 ) ( + , %s ) e. dom ~~> )' % (A0, TWO, GN))
equ3 = w.s([], 'eqid', '%s = ( ZZ>= ` ( %s + 1 ) )' % (U3, TWO))
tlcl3 = w.s([equ3, tw1z, vGv, trmcv, cvg3], 'isumcl', '( %s -> sum_ k e. %s %s e. CC )' % (A0, U3, TRMK))
tlb = w.s([w.s([tlcl3], 'abscld', '( %s -> ( abs ` sum_ k e. %s %s ) e. RR )' % (A0, U3, TRMK)), qre, hre,
           w.s([tl, mulq], 'breqtrd',
               '( %s -> ( abs ` sum_ k e. %s %s ) <_ ( ( %s ^c ( 1 - %s ) ) / ( %s - 1 ) ) )' % (A0, U3, TRMK, TWO, RZ, RZ)),
           qle], 'letrd', '( %s -> ( abs ` sum_ k e. %s %s ) <_ ( 1 / 2 ) )' % (A0, U3, TRMK))
# the decomposition
WW = '( ( %s ` %s ) + sum_ k e. %s %s )' % (GN, TWO, U3, TRMK)
SNN = 'sum_ k e. NN %s' % TRMK
axtwo = w.s([w.s([nx, twon], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ %s e. NN ) )' % (A0, DC, TWO)),
             w.inst('lchrval')], 'syl', '( %s -> ( %s ` %s ) = ( X ` ( %s ` %s ) ) )' % (A0, AX, TWO, LH, TWO))
cltwo = w.s([w.s([w.s([nx, twon], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ %s e. NN ) )' % (A0, DC, TWO)),
                  w.inst('lchrcl')], 'syl', '( %s -> ( X ` ( %s ` %s ) ) e. CC )' % (A0, LH, TWO))], 'idi',
            '( %s -> ( X ` ( %s ` %s ) ) e. CC )' % (A0, LH, TWO))
axtwoc = w.s([axtwo, cltwo], 'eqeltrd', '( %s -> ( %s ` %s ) e. CC )' % (A0, AX, TWO))
ptwo = w.s([w.s([twrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, TWO)),
            w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')], 'syl2anc',
           '( %s -> ( %s ^c -u Z ) e. CC )' % (A0, TWO))
g2cl = w.s([vG2, w.s([axtwoc, ptwo], 'mulcld', '( %s -> ( ( %s ` %s ) x. ( %s ^c -u Z ) ) e. CC )' % (A0, AX, TWO, TWO))],
           'eqeltrd', '( %s -> ( %s ` %s ) e. CC )' % (A0, GN, TWO))
wcl = w.s([g2cl, tlcl3], 'addcld', '( %s -> %s e. CC )' % (A0, WW))
eq1 = w.s([w.s([first2, sp2], 'oveq12d', '( %s -> ( ( %s ` 1 ) + sum_ k e. %s %s ) = ( 1 + %s ) )' % (A0, GN, U2, TRMK, WW))], 'idi',
          '( %s -> ( ( %s ` 1 ) + sum_ k e. %s %s ) = ( 1 + %s ) )' % (A0, GN, U2, TRMK, WW))
eqS = w.s([sp1, eq1], 'eqtrd', '( %s -> %s = ( 1 + %s ) )' % (A0, SNN, WW))
onec = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0)
sub = w.s([w.s([eqS], 'oveq1d', '( %s -> ( %s - %s ) = ( ( 1 + %s ) - %s ) )' % (A0, SNN, WW, WW, WW)),
           w.s([onec, wcl], 'pncand', '( %s -> ( ( 1 + %s ) - %s ) = 1 )' % (A0, WW, WW))], 'eqtrd',
          '( %s -> ( %s - %s ) = 1 )' % (A0, SNN, WW))
scl = w.s([dsh, w.inst('dsercl')], 'syl', '( %s -> %s e. CC )' % (A0, SNN))
absW = w.s([w.s([g2cl, tlcl3], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` ( %s ` %s ) ) + ( abs ` sum_ k e. %s %s ) ) )' % (A0, WW, GN, TWO, U3, TRMK))], 'idi',
           '( %s -> ( abs ` %s ) <_ ( ( abs ` ( %s ` %s ) ) + ( abs ` sum_ k e. %s %s ) ) )' % (A0, WW, GN, TWO, U3, TRMK))
ag2 = w.s([g2cl], 'abscld', '( %s -> ( abs ` ( %s ` %s ) ) e. RR )' % (A0, GN, TWO))
atl = w.s([tlcl3], 'abscld', '( %s -> ( abs ` sum_ k e. %s %s ) e. RR )' % (A0, U3, TRMK))
awr = w.s([wcl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, WW))
absW2 = linarith(w, A0, [absW, t2b, tlb], '( abs ` %s ) <_ ( 3 / 4 )' % WW,
                 leaves={'( abs ` %s )' % WW: awr, '( abs ` ( %s ` %s ) )' % (GN, TWO): ag2,
                         '( abs ` sum_ k e. %s %s )' % (U3, TRMK): atl})
tri = w.s([scl, wcl, w.inst('abs2dif2')], 'syl2anc',
          '( %s -> ( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, SNN, WW, SNN, WW))
tri2 = w.s([w.s([w.s([sub], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` 1 ) )' % (A0, SNN, WW)),
                 w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % A0)], 'eqtrd',
                '( %s -> ( abs ` ( %s - %s ) ) = 1 )' % (A0, SNN, WW)), tri], 'eqbrtrrd',
           '( %s -> 1 <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, SNN, WW))
asr = w.s([scl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, SNN))
fin = linarith(w, A0, [tri2, absW2], '( 1 / 4 ) <_ ( abs ` %s )' % SNN,
               leaves={'( abs ` %s )' % SNN: asr, '( abs ` %s )' % WW: awr})
# rewrite the coefficients
Akk = '( %s /\\ k e. NN )' % A0
ser = w.s([w.s([axk], 'oveq1d', '( %s -> %s = %s )' % (Akk, TRMK, XTRMK))], 'sumeq2dv',
          '( %s -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, TRMK, XTRMK))
w.qed([fin, w.s([ser], 'fveq2d', '( %s -> ( abs ` sum_ k e. NN %s ) = ( abs ` sum_ k e. NN %s ) )' % (A0, TRMK, XTRMK))],
      'breqtrd', '( %s -> ( 1 / 4 ) <_ ( abs ` sum_ k e. NN %s ) )' % (A0, XTRMK)); run3(w)
