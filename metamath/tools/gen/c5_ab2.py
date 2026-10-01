"""C5, the character corollaries of the agreement block: LSeries_eq_Afun,
norm_LFunction_le_of_re_pos and norm_LFunction_le_of_one_quarter_le_re for a
nonprincipal character, with the continued L-function being the Abel series."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

RZ = '( Re ` Z )'
AX = '( q e. NN |-> %s )' % CHV('q')
CFBX = '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (AX, AX)
DIF = lambda k: '( ( %s ^c -u Z ) - ( ( %s + 1 ) ^c -u Z ) )' % (k, k)
CATM = lambda k: '( %s x. %s )' % (CSUM(k), DIF(k))
CSFV = CSF()
CSFA = lambda k: '( ( %s ` %s ) x. %s )' % (CSFV, k, DIF(k))


def csfval(w, ante, k, mk):
    sub = w.s([w.s([], 'oveq2', '( q = %s -> ( 1 ... q ) = ( 1 ... %s ) )' % (k, k))], 'sumeq1d', '( q = %s -> %s = %s )' % (k, CSUM('q'), CSUM(k)))
    return mpv(w, ante, CSFV, k, CSUM(k), sub, mk, vexd(w, ante, CSUM(k), 'sum'))


def axsum(w, ante, k, nx, mk):
    """( ante -> sum_ i e. ( 1 ... k ) ( AX ` i ) = CSUM(k) ) from nx: ( N e. NN /\\ X e. DC ), mk: k e. NN"""
    Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (ante, k)
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, k)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
    lv = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ai, DC)), inn], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ i e. NN ) )' % (Ai, DC)),
              w.inst('lchrval')], 'syl', '( %s -> ( %s ` i ) = %s )' % (Ai, AX, CHV('i')))
    return w.s([lv], 'sumeq2dv', '( %s -> sum_ i e. ( 1 ... %s ) ( %s ` i ) = %s )' % (ante, k, AX, CSUM(k)))


# ---------------------------------------------------------------- lchragr
w = W('lchragr', 'The Abel series of a nonprincipal Dirichlet character agrees with its L-series to the right '
      'of the line one: Lean\'s ` LSeries_eq_Afun ` of LGrowth.lean ( ~ abagr at ~ lchrcfb , ~ lchrcsf ).')
ZP1 = '( Z e. CC /\\ 1 < %s )' % RZ
A0 = '( %s /\\ %s )' % (CHR, ZP1)
chr_ = w.s([], 'simpl', '( %s -> %s )' % (A0, CHR))
zp = w.s([], 'simpr', '( %s -> %s )' % (A0, ZP1))
nx = w.s([chr_, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))
nn = w.s([nx, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
cfbx = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX))
csf = w.s([chr_, w.inst('lchrcsf')], 'syl', '( %s -> ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) )' % (A0, CSFV, CSFV))
bq = w.s([csf, w.inst('simp3')], 'syl', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ N )' % (A0, CSFV))
Am = '( %s /\\ m e. NN )' % A0
mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
cv = csfval(w, Am, 'm', mn)
asm = axsum(w, Am, 'm', w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Am, DC)), mn)
eqm = w.s([w.s([cv, asm], 'eqtr4d', '( %s -> ( %s ` m ) = sum_ i e. ( 1 ... m ) ( %s ` i ) )' % (Am, CSFV, AX))], 'fveq2d',
          '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) )' % (Am, CSFV, AX))
imp = w.s([w.s([eqm], 'breq1d', '( %s -> ( ( abs ` ( %s ` m ) ) <_ N <-> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N ) )' % (Am, CSFV, AX))], 'biimpd',
          '( %s -> ( ( abs ` ( %s ` m ) ) <_ N -> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N ) )' % (Am, CSFV, AX))
bq2 = w.s([bq, w.s([imp], 'ralimdva', '( %s -> ( A. m e. NN ( abs ` ( %s ` m ) ) <_ N -> A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N ) )' % (A0, CSFV, AX))],
          'mpd', '( %s -> A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N )' % (A0, AX))
ABSPX = '( N e. RR /\\ A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N )' % AX
pack = w.s([w.s([cfbx, zp], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX, ZP1)), w.s([w.s([nn], 'nnred', '( %s -> N e. RR )' % A0), bq2], 'jca', '( %s -> %s )' % (A0, ABSPX))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ %s ) )' % (A0, CFBX, ZP1, ABSPX))
ATMX = '( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s )' % (AX, DIF('k'))
ag = w.s([pack, w.inst('abagr')], 'syl', '( %s -> sum_ k e. NN %s = sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) )' % (A0, ATMX, AX))
Ak = '( %s /\\ k e. NN )' % A0
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
nxk = w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ak, DC))
lhs = w.s([w.s([axsum(w, Ak, 'k', nxk, kn)], 'oveq1d', '( %s -> %s = %s )' % (Ak, ATMX, CATM('k')))], 'sumeq2dv',
          '( %s -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, ATMX, CATM('k')))
lvk = w.s([w.s([nxk, kn], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Ak, DC)), w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, AX, CHV('k')))
rhs = w.s([w.s([lvk], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( %s x. ( k ^c -u Z ) ) )' % (Ak, AX, CHV('k')))], 'sumeq2dv',
          '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )' % (A0, AX, CHV('k')))
w.qed([w.s([lhs, ag], 'eqtr3d', '( %s -> sum_ k e. NN %s = sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) )' % (A0, CATM('k'), AX)), rhs], 'eqtrd',
      '( %s -> sum_ k e. NN %s = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )' % (A0, CATM('k'), CHV('k')))
run5(w)

# ---------------------------------------------------------------- lchrab
w = W('lchrab', 'The bound on the continued L-function of a nonprincipal character on the right half-plane: '
      'Lean\'s ` norm_LFunction_le_of_re_pos ` of LGrowth.lean ( ~ abbnd at ~ lchrcsf ).')
ZP0 = '( Z e. CC /\\ 0 < %s )' % RZ
A0 = '( %s /\\ %s )' % (CHR, ZP0)
BND = '( ( N x. ( abs ` Z ) ) x. ( 1 + ( 1 / %s ) ) )' % RZ
chr_ = w.s([], 'simpl', '( %s -> %s )' % (A0, CHR))
zp = w.s([], 'simpr', '( %s -> %s )' % (A0, ZP0))
csf = w.s([chr_, w.inst('lchrcsf')], 'syl', '( %s -> ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) )' % (A0, CSFV, CSFV))
bd = w.s([w.s([csf, zp], 'jca', '( %s -> ( ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) /\\ %s ) )' % (A0, CSFV, CSFV, ZP0)), w.inst('abbnd')], 'syl',
          '( %s -> ( abs ` sum_ k e. NN %s ) <_ %s )' % (A0, CSFA('k'), BND))
Ak = '( %s /\\ k e. NN )' % A0
cv = csfval(w, Ak, 'k', w.s([], 'simpr', '( %s -> k e. NN )' % Ak))
rw = w.s([w.s([w.s([cv], 'oveq1d', '( %s -> %s = %s )' % (Ak, CSFA('k'), CATM('k')))], 'sumeq2dv', '( %s -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, CSFA('k'), CATM('k')))],
         'fveq2d', '( %s -> ( abs ` sum_ k e. NN %s ) = ( abs ` sum_ k e. NN %s ) )' % (A0, CSFA('k'), CATM('k')))
w.qed([rw, bd], 'eqbrtrrd', '( %s -> ( abs ` sum_ k e. NN %s ) <_ %s )' % (A0, CATM('k'), BND))
run5(w)

# ---------------------------------------------------------------- lchrab4
w = W('lchrab4', 'The numeral bound on the continued L-function of a nonprincipal character for '
      '` ( 1 / 4 ) <_ ( Re ` Z ) ` : Lean\'s ` norm_LFunction_le_of_one_quarter_le_re ` of LGrowth.lean.')
ZP4 = '( Z e. CC /\\ ( 1 / 4 ) <_ %s )' % RZ
A0 = '( %s /\\ %s )' % (CHR, ZP4)
L = 'sum_ k e. NN %s' % CATM('k')
AZ = '( abs ` Z )'
chr_ = w.s([], 'simpl', '( %s -> %s )' % (A0, CHR))
nn = w.s([w.s([chr_, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC)), w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
nr = w.s([nn], 'nnred', '( %s -> N e. RR )' % A0)
nge = w.s([w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A0)], 'rpge0d', '( %s -> 0 <_ N )' % A0)
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
q4 = w.s([], 'simprr', '( %s -> ( 1 / 4 ) <_ %s )' % (A0, RZ))
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
r4 = a1(w, A0, '4re', '4 e. RR')
p4 = a1(w, A0, '4pos', '0 < 4')
rp4 = w.s([r4, p4], 'elrpd', '( %s -> 4 e. RR+ )' % A0)
q4rp = w.s([rp4], 'rpreccld', '( %s -> ( 1 / 4 ) e. RR+ )' % A0)
q4r = w.s([q4rp], 'rpred', '( %s -> ( 1 / 4 ) e. RR )' % A0)
q4p = w.s([q4rp], 'rpgt0d', '( %s -> 0 < ( 1 / 4 ) )' % A0)
z0 = w.s([a1(w, A0, '0re', '0 e. RR'), q4r, rz, q4p, q4], 'ltletrd', '( %s -> 0 < %s )' % (A0, RZ))
bd = w.s([w.s([chr_, w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < %s ) )' % (A0, RZ))], 'jca', '( %s -> ( %s /\\ ( Z e. CC /\\ 0 < %s ) ) )' % (A0, CHR, RZ)), w.inst('lchrab')], 'syl',
          '( %s -> ( abs ` %s ) <_ ( ( N x. %s ) x. ( 1 + ( 1 / %s ) ) ) )' % (A0, L, AZ, RZ))
# 1 / Re Z <_ 4
rec = w.s([w.s([w.s([q4r, q4p], 'jca', '( %s -> ( ( 1 / 4 ) e. RR /\\ 0 < ( 1 / 4 ) ) )' % A0), w.s([rz, z0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, RZ, RZ)), w.inst('lerec')],
              'syl2anc', '( %s -> ( ( 1 / 4 ) <_ %s <-> ( 1 / %s ) <_ ( 1 / ( 1 / 4 ) ) ) )' % (A0, RZ, RZ))], 'idi',
         '( %s -> ( ( 1 / 4 ) <_ %s <-> ( 1 / %s ) <_ ( 1 / ( 1 / 4 ) ) ) )' % (A0, RZ, RZ))
rec2 = w.s([q4, rec], 'mpbid', '( %s -> ( 1 / %s ) <_ ( 1 / ( 1 / 4 ) ) )' % (A0, RZ))
rr = w.s([w.s([r4], 'recnd', '( %s -> 4 e. CC )' % A0), w.s([rp4], 'rpne0d', '( %s -> 4 =/= 0 )' % A0), w.inst('recrec')], 'syl2anc', '( %s -> ( 1 / ( 1 / 4 ) ) = 4 )' % A0)
rec3 = w.s([rec2, rr], 'breqtrd', '( %s -> ( 1 / %s ) <_ 4 )' % (A0, RZ))
irz = w.s([w.s([w.s([rz, z0], 'elrpd', '( %s -> %s e. RR+ )' % (A0, RZ))], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (A0, RZ))], 'rpred', '( %s -> ( 1 / %s ) e. RR )' % (A0, RZ))
r1 = a1(w, A0, '1re', '1 e. RR')
le5a = w.s([irz, r4, r1, rec3], 'leadd1dd', '( %s -> ( ( 1 / %s ) + 1 ) <_ ( 4 + 1 ) )' % (A0, RZ))
cm = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), w.s([irz], 'recnd', '( %s -> ( 1 / %s ) e. CC )' % (A0, RZ))], 'addcomd', '( %s -> ( 1 + ( 1 / %s ) ) = ( ( 1 / %s ) + 1 ) )' % (A0, RZ, RZ))
le5 = w.s([w.s([cm, le5a], 'eqbrtrd', '( %s -> ( 1 + ( 1 / %s ) ) <_ ( 4 + 1 ) )' % (A0, RZ)), a1(w, A0, '4p1e5', '( 4 + 1 ) = 5')], 'breqtrd',
          '( %s -> ( 1 + ( 1 / %s ) ) <_ 5 )' % (A0, RZ))
# the products
az = w.s([zc], 'abscld', '( %s -> %s e. RR )' % (A0, AZ))
az0 = w.s([zc], 'absge0d', '( %s -> 0 <_ %s )' % (A0, AZ))
W_ = '( N x. %s )' % AZ
wr = w.s([nr, az], 'remulcld', '( %s -> %s e. RR )' % (A0, W_))
w0 = w.s([nr, az, nge, az0], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, W_))
o5 = w.s([r1, irz], 'readdcld', '( %s -> ( 1 + ( 1 / %s ) ) e. RR )' % (A0, RZ))
r5 = a1(w, A0, '5re', '5 e. RR')
m1 = w.s([w.s([o5, r5, w.s([wr, w0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, W_, W_))], '3jca', '( %s -> ( ( 1 + ( 1 / %s ) ) e. RR /\\ 5 e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A0, RZ, W_, W_)),
           le5, w.inst('lemul2a')], 'syl2anc', '( %s -> ( %s x. ( 1 + ( 1 / %s ) ) ) <_ ( %s x. 5 ) )' % (A0, W_, RZ, W_))
r2 = a1(w, A0, '2re', '2 e. RR')
zle = w.s([w.s([a1(w, A0, '0le2', '0 <_ 2'), w.s([r2, az, w.inst('addge02')], 'syl2anc', '( %s -> ( 0 <_ 2 <-> %s <_ ( 2 + %s ) ) )' % (A0, AZ, AZ))], 'mpbid',
               '( %s -> %s <_ ( 2 + %s ) )' % (A0, AZ, AZ))], 'idi', '( %s -> %s <_ ( 2 + %s ) )' % (A0, AZ, AZ))
V_ = '( N x. ( 2 + %s ) )' % AZ
twz = w.s([r2, az], 'readdcld', '( %s -> ( 2 + %s ) e. RR )' % (A0, AZ))
wv = w.s([w.s([az, twz, w.s([nr, nge], 'jca', '( %s -> ( N e. RR /\\ 0 <_ N ) )' % A0)], '3jca', '( %s -> ( %s e. RR /\\ ( 2 + %s ) e. RR /\\ ( N e. RR /\\ 0 <_ N ) ) )' % (A0, AZ, AZ)), zle,
           w.inst('lemul2a')], 'syl2anc', '( %s -> %s <_ %s )' % (A0, W_, V_))
vr = w.s([nr, twz], 'remulcld', '( %s -> %s e. RR )' % (A0, V_))
p5 = w.s([a1(w, A0, '0re', '0 e. RR'), r5, a1(w, A0, '5pos', '0 < 5')], 'ltled', '( %s -> 0 <_ 5 )' % A0)
m2 = w.s([w.s([wr, vr, w.s([r5, p5], 'jca', '( %s -> ( 5 e. RR /\\ 0 <_ 5 ) )' % A0)], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( 5 e. RR /\\ 0 <_ 5 ) ) )' % (A0, W_, V_)), wv,
           w.inst('lemul1a')], 'syl2anc', '( %s -> ( %s x. 5 ) <_ ( %s x. 5 ) )' % (A0, W_, V_))
alg = w.s([w.s([w.s([nr], 'recnd', '( %s -> N e. CC )' % A0), w.s([twz], 'recnd', '( %s -> ( 2 + %s ) e. CC )' % (A0, AZ)), w.s([r5], 'recnd', '( %s -> 5 e. CC )' % A0)], 'mul32d',
               '( %s -> ( %s x. 5 ) = ( ( N x. 5 ) x. ( 2 + %s ) ) )' % (A0, V_, AZ)),
           w.s([w.s([w.s([nr], 'recnd', '( %s -> N e. CC )' % A0), w.s([r5], 'recnd', '( %s -> 5 e. CC )' % A0)], 'mulcomd', '( %s -> ( N x. 5 ) = ( 5 x. N ) )' % A0)], 'oveq1d',
               '( %s -> ( ( N x. 5 ) x. ( 2 + %s ) ) = ( ( 5 x. N ) x. ( 2 + %s ) ) )' % (A0, AZ, AZ))], 'eqtrd', '( %s -> ( %s x. 5 ) = ( ( 5 x. N ) x. ( 2 + %s ) ) )' % (A0, V_, AZ))
csf = w.s([chr_, w.inst('lchrcsf')], 'syl', '( %s -> ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) )' % (A0, CSFV, CSFV))
scl0 = w.s([w.s([csf, w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < %s ) )' % (A0, RZ))], 'jca',
                '( %s -> ( ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) /\\ ( Z e. CC /\\ 0 < %s ) ) )' % (A0, CSFV, CSFV, RZ)), w.inst('abcl')], 'syl',
           '( %s -> sum_ k e. NN %s e. CC )' % (A0, CSFA('k')))
Ak = '( %s /\\ k e. NN )' % A0
cv = csfval(w, Ak, 'k', w.s([], 'simpr', '( %s -> k e. NN )' % Ak))
rw = w.s([w.s([cv], 'oveq1d', '( %s -> %s = %s )' % (Ak, CSFA('k'), CATM('k')))], 'sumeq2dv', '( %s -> sum_ k e. NN %s = %s )' % (A0, CSFA('k'), L))
scl = w.s([rw, scl0], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, L))
absr = w.s([scl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, L))
wo5 = w.s([wr, o5], 'remulcld', '( %s -> ( %s x. ( 1 + ( 1 / %s ) ) ) e. RR )' % (A0, W_, RZ))
w5 = w.s([wr, r5], 'remulcld', '( %s -> ( %s x. 5 ) e. RR )' % (A0, W_))
v5 = w.s([vr, r5], 'remulcld', '( %s -> ( %s x. 5 ) e. RR )' % (A0, V_))
t1 = w.s([absr, wo5, w5, bd, m1], 'letrd', '( %s -> ( abs ` %s ) <_ ( %s x. 5 ) )' % (A0, L, W_))
t2 = w.s([absr, w5, v5, t1, m2], 'letrd', '( %s -> ( abs ` %s ) <_ ( %s x. 5 ) )' % (A0, L, V_))
w.qed([t2, alg], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( ( 5 x. N ) x. ( 2 + %s ) ) )' % (A0, L, AZ))
run5(w)
