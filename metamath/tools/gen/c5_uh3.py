"""C5, generic block 3: the derivative term-function sequence, the derivative of
a partial-sum function, the derivative of the sum function (ulmdv) and HOL."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

PS = PSQ('F'); DFF = DF(); PSD = PSQ(DFF)
FM = FMAP('F'); FMD = FMAP(DFF)
UM = UHM('F', 'M'); UD = UHD('F', 'R'); UMD = UHM(DFF, 'R')
UT = UHT('F')
A0 = UH()
G = GSUM(); H = HSUM(); GD = GSUM(DFF)
UHS0 = UHS(); UHSD = UHS(DFF, 'R')
HOLJ = HOLG2('( F ` j )', 'U')


def HOLK(k):
    return HOLG2('( F ` %s )' % k, 'U')


def ctx(w, A1, uh=None):
    d = {}
    if uh is None:
        uh = w.s([], 'id', '( %s -> %s )' % (A1, A0))
    d['uh'] = uh
    l = w.s([uh, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A1, FM, UT))
    r = w.s([uh, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A1, UM, UD))
    d['ff'] = w.s([l, w.inst('simpl')], 'syl', '( %s -> %s )' % (A1, FM))
    d['ut'] = w.s([l, w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, UT))
    d['um'] = w.s([r, w.inst('simpl')], 'syl', '( %s -> %s )' % (A1, UM))
    d['ud'] = w.s([r, w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, UD))
    d['uhs'] = w.s([d['ff'], d['um']], 'jca', '( %s -> %s )' % (A1, UHS0))
    d['nu1'], d['z1'], d['n1'] = nnuz(w, A1)
    d['u1n'] = w.s([w.s([d['nu1']], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A1)
    d['ue'] = uex(w, A1, d['ff'], d['n1'])
    return d


def holk(w, ante, k, ut, mk):
    """( ante -> HOL(( F ` k ),U) ) from the termwise quantifier ut and mk: k e. NN"""
    fe = w.s([], 'fveq2', '( j = %s -> ( F ` j ) = ( F ` %s ) )' % (k, k))
    e1 = w.s([fe], 'eleq1d', '( j = %s -> ( ( F ` j ) e. ( U -cn-> CC ) <-> ( F ` %s ) e. ( U -cn-> CC ) ) )' % (k, k))
    e2 = w.s([w.s([w.s([fe], 'oveq2d', '( j = %s -> ( CC _D ( F ` j ) ) = ( CC _D ( F ` %s ) ) )' % (k, k))], 'dmeqd',
                  '( j = %s -> dom ( CC _D ( F ` j ) ) = dom ( CC _D ( F ` %s ) ) )' % (k, k))], 'sseq2d',
             '( j = %s -> ( U C_ dom ( CC _D ( F ` j ) ) <-> U C_ dom ( CC _D ( F ` %s ) ) ) )' % (k, k))
    sb = w.s([e1, e2], 'anbi12d', '( j = %s -> ( %s <-> %s ) )' % (k, HOLJ, HOLK(k)))
    return w.s([sb, ut, mk], 'rspcdva', '( %s -> %s )' % (ante, HOLK(k)))


def dfval(w, ante, k, mk):
    """( ante -> ( DF ` k ) = ( CC _D ( F ` k ) ) )"""
    s = w.s([w.s([], 'fveq2', '( h = %s -> ( F ` h ) = ( F ` %s ) )' % (k, k))], 'oveq2d',
            '( h = %s -> ( CC _D ( F ` h ) ) = ( CC _D ( F ` %s ) ) )' % (k, k))
    return mpv(w, ante, DFF, k, '( CC _D ( F ` %s ) )' % k, s, mk, vexd(w, ante, '( CC _D ( F ` %s ) )' % k, 'ov'))


def uopn(w, ante, d):
    """( ante -> U e. TOP ) from the termwise HOL at 1"""
    h1 = holk(w, ante, '1', d['ut'], d['n1'])
    return w.s([h1, w.inst('holopn')], 'syl', '( %s -> U e. %s )' % (ante, TOP))


# ---------------------------------------------------------------- uhdf
w = W('uhdf', 'The derivative term-function sequence of a holomorphic term-function sequence '
      'with a summable majorant for the derivatives is itself a majorised term-function sequence.')
d = ctx(w, A0)
Ah = '( %s /\\ h e. NN )' % A0
hn = w.s([], 'simpr', '( %s -> h e. NN )' % Ah)
hk = holk(w, Ah, 'h', w.s([d['ut']], 'adantr', '( %s -> %s )' % (Ah, UT)), hn)
dff = w.s([hk, w.inst('holf')], 'syl', '( %s -> ( CC _D ( F ` h ) ) : U --> CC )' % Ah)
dfm = elmapf(w, Ah, '( CC _D ( F ` h ) )', w.s([d['ue']], 'adantr', '( %s -> U e. _V )' % Ah), dff)
dfmap = w.s([dfm, w.s([], 'eqid', '%s = %s' % (DFF, DFF))], 'fmptd', '( %s -> %s )' % (A0, FMD))
rf = w.s([d['ud'], w.inst('simp1')], 'syl', '( %s -> R : NN --> RR )' % A0)
rcv = w.s([d['ud'], w.inst('simp2')], 'syl', '( %s -> seq 1 ( + , R ) e. dom ~~> )' % A0)
rb = w.s([d['ud'], w.inst('simp3')], 'syl', '( %s -> A. j e. NN A. y e. U ( abs ` ( ( CC _D ( F ` j ) ) ` y ) ) <_ ( R ` j ) )' % A0)
# the bound in the form of the mapping DF: a closed biconditional
jn = w.s([], 'id', '( j e. NN -> j e. NN )')
dv = dfval(w, 'j e. NN', 'j', jn)
e1 = w.s([w.s([w.s([dv], 'fveq1d', '( j e. NN -> ( ( %s ` j ) ` y ) = ( ( CC _D ( F ` j ) ) ` y ) )' % DFF)], 'fveq2d',
              '( j e. NN -> ( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` ( ( CC _D ( F ` j ) ) ` y ) ) )' % DFF)], 'breq1d',
         '( j e. NN -> ( ( abs ` ( ( %s ` j ) ` y ) ) <_ ( R ` j ) <-> ( abs ` ( ( CC _D ( F ` j ) ) ` y ) ) <_ ( R ` j ) ) )' % DFF)
e2 = w.s([e1], 'ralbidv', '( j e. NN -> ( A. y e. U ( abs ` ( ( %s ` j ) ` y ) ) <_ ( R ` j ) <-> A. y e. U ( abs ` ( ( CC _D ( F ` j ) ) ` y ) ) <_ ( R ` j ) ) )' % DFF)
e3 = w.s([e2], 'ralbiia', '( A. j e. NN A. y e. U ( abs ` ( ( %s ` j ) ` y ) ) <_ ( R ` j ) <-> A. j e. NN A. y e. U ( abs ` ( ( CC _D ( F ` j ) ) ` y ) ) <_ ( R ` j ) )' % DFF)
rb2 = w.s([rb, w.s([e3], 'a1i', '( %s -> ( A. j e. NN A. y e. U ( abs ` ( ( %s ` j ) ` y ) ) <_ ( R ` j ) <-> A. j e. NN A. y e. U ( abs ` ( ( CC _D ( F ` j ) ) ` y ) ) <_ ( R ` j ) ) )' % (A0, DFF))],
          'mpbird', '( %s -> A. j e. NN A. y e. U ( abs ` ( ( %s ` j ) ` y ) ) <_ ( R ` j ) )' % (A0, DFF))
w.qed([dfmap, w.s([rf, rcv, rb2], '3jca', '( %s -> %s )' % (A0, UMD))], 'jca', '( %s -> %s )' % (A0, UHSD))
run5(w)

# ---------------------------------------------------------------- uhdps
w = W('uhdps', 'The derivative of a partial-sum function is the partial-sum function of the '
      'derivative term-function sequence ( ~ dvmptfsum ).')
A1 = '( %s /\\ N e. NN )' % A0
d = ctx(w, A1, w.s([], 'simpl', '( %s -> %s )' % (A1, A0)))
nn = w.s([], 'simpr', '( %s -> N e. NN )' % A1)
psv = w.s([w.s([d['ff'], nn], 'jca', '( %s -> ( %s /\\ N e. NN ) )' % (A1, FM)), w.inst('uhps')], 'syl',
          '( %s -> ( %s ` N ) = %s )' % (A1, PS, PSMAP('F', 'N')))
# dvmptfsum
ej = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
sc = a1(w, A1, 'cnelprrecn', 'CC e. { RR , CC }')
uo = uopn(w, A1, d)
fin = w.s([], 'fzfid', '( %s -> ( 1 ... N ) e. Fin )' % A1)
Akz = '( %s /\\ k e. ( 1 ... N ) /\\ z e. U )' % A1
kn = w.s([w.s([], 'simp2', '( %s -> k e. ( 1 ... N ) )' % Akz), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Akz)
zu = w.s([], 'simp3', '( %s -> z e. U )' % Akz)
ffk = w.s([d['ff']], '3ad2ant1', '( %s -> %s )' % (Akz, FM))
fkf = fval(w, Akz, 'k', kn, ffk)
ha = w.s([fkf, zu], 'ffvelcdmd', '( %s -> ( ( F ` k ) ` z ) e. CC )' % Akz)
hk = holk(w, Akz, 'k', w.s([d['ut']], '3ad2ant1', '( %s -> %s )' % (Akz, UT)), kn)
hb = w.s([w.s([hk, w.inst('holf')], 'syl', '( %s -> ( CC _D ( F ` k ) ) : U --> CC )' % Akz), zu], 'ffvelcdmd',
         '( %s -> ( ( CC _D ( F ` k ) ) ` z ) e. CC )' % Akz)
Ak = '( %s /\\ k e. ( 1 ... N ) )' % A1
kn2 = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % Ak), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ak)
hk2 = holk(w, Ak, 'k', w.s([d['ut']], 'adantr', '( %s -> %s )' % (Ak, UT)), kn2)
hd = w.s([hk2, w.inst('holdv')], 'syl',
         '( %s -> ( CC _D ( z e. U |-> ( ( F ` k ) ` z ) ) ) = ( z e. U |-> ( ( CC _D ( F ` k ) ) ` z ) ) )' % Ak)
HN = '( z e. U |-> sum_ k e. ( 1 ... N ) ( ( CC _D ( F ` k ) ) ` z ) )'
dvs = w.s([ej, ek, sc, uo, fin, ha, hb, hd], 'dvmptfsum', '( %s -> ( CC _D %s ) = %s )' % (A1, PSMAP('F', 'N'), HN))
# the partial sum of DF
dfmap = w.s([w.s([d['uh'], w.inst('uhdf')], 'syl', '( %s -> %s )' % (A1, UHSD)), w.inst('simpl')], 'syl', '( %s -> %s )' % (A1, FMD))
psd = w.s([w.s([dfmap, nn], 'jca', '( %s -> ( %s /\\ N e. NN ) )' % (A1, FMD)), w.inst('uhps')], 'syl',
          '( %s -> ( %s ` N ) = %s )' % (A1, PSD, PSMAP(DFF, 'N')))
Azk = '( ( %s /\\ z e. U ) /\\ k e. ( 1 ... N ) )' % A1
kn3 = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % Azk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Azk)
dv3 = w.s([dfval(w, Azk, 'k', kn3)], 'fveq1d', '( %s -> ( ( %s ` k ) ` z ) = ( ( CC _D ( F ` k ) ) ` z ) )' % (Azk, DFF))
sm = w.s([dv3], 'sumeq2dv', '( ( %s /\\ z e. U ) -> sum_ k e. ( 1 ... N ) ( ( %s ` k ) ` z ) = sum_ k e. ( 1 ... N ) ( ( CC _D ( F ` k ) ) ` z ) )' % (A1, DFF))
mpe = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A1, PSMAP(DFF, 'N'), HN))
psd2 = w.s([psd, mpe], 'eqtrd', '( %s -> ( %s ` N ) = %s )' % (A1, PSD, HN))
w.qed([w.s([w.s([psv], 'oveq2d', '( %s -> ( CC _D ( %s ` N ) ) = ( CC _D %s ) )' % (A1, PS, PSMAP('F', 'N'))), dvs], 'eqtrd',
           '( %s -> ( CC _D ( %s ` N ) ) = %s )' % (A1, PS, HN)), psd2], 'eqtr4d',
      '( %s -> ( CC _D ( %s ` N ) ) = ( %s ` N ) )' % (A1, PS, PSD))
run5(w)

# ---------------------------------------------------------------- uhdv
w = W('uhdv', 'The derivative of the sum of a holomorphic term-function sequence with summable '
      'majorants for the terms and their derivatives is the sum of the derivatives ( ~ ulmdv ). '
      'This is the derivative half of Mathlib\'s ` differentiableOn_tsum_of_summable_norm `.')
d = ctx(w, A0)
sc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
psf = w.s([d['ff'], w.inst('uhpsf')], 'syl', '( %s -> %s : NN --> ( CC ^m U ) )' % (A0, PS))
gf = w.s([d['uhs'], w.inst('uhf')], 'syl', '( %s -> %s : U --> CC )' % (A0, G))
Aw = '( %s /\\ w e. U )' % A0
ptl = w.s([w.s([w.s([d['uhs']], 'adantr', '( %s -> %s )' % (Aw, UHS0)), w.s([], 'simpr', '( %s -> w e. U )' % Aw)], 'jca',
                '( %s -> ( %s /\\ w e. U ) )' % (Aw, UHS0)), w.inst('uhptl')], 'syl',
          '( %s -> ( i e. NN |-> ( ( %s ` i ) ` w ) ) ~~> ( %s ` w ) )' % (Aw, PS, G))
# the derivative sequence is PSD
Ai = '( %s /\\ i e. NN )' % A0
dps = w.s([w.s([w.s([d['uh']], 'adantr', '( %s -> %s )' % (Ai, A0)), w.s([], 'simpr', '( %s -> i e. NN )' % Ai)], 'jca',
                '( %s -> ( %s /\\ i e. NN ) )' % (Ai, A0)), w.inst('uhdps')], 'syl',
          '( %s -> ( CC _D ( %s ` i ) ) = ( %s ` i ) )' % (Ai, PS, PSD))
m1 = w.s([dps], 'mpteq2dva', '( %s -> ( i e. NN |-> ( CC _D ( %s ` i ) ) ) = ( i e. NN |-> ( %s ` i ) ) )' % (A0, PS, PSD))
fn = w.s([w.s([d['z1'], w.inst('seqfn')], 'syl', '( %s -> %s Fn ( ZZ>= ` 1 ) )' % (A0, PSD)),
          w.s([d['u1n']], 'fneq2d', '( %s -> ( %s Fn ( ZZ>= ` 1 ) <-> %s Fn NN ) )' % (A0, PSD, PSD))], 'mpbid',
         '( %s -> %s Fn NN )' % (A0, PSD))
bi = w.s([], 'dffn5', '( %s Fn NN <-> %s = ( i e. NN |-> ( %s ` i ) ) )' % (PSD, PSD, PSD))
eqm = w.s([fn, w.s([bi], 'a1i', '( %s -> ( %s Fn NN <-> %s = ( i e. NN |-> ( %s ` i ) ) ) )' % (A0, PSD, PSD, PSD))], 'mpbid',
          '( %s -> %s = ( i e. NN |-> ( %s ` i ) ) )' % (A0, PSD, PSD))
ident = w.s([m1, w.s([eqm], 'eqcomd', '( %s -> ( i e. NN |-> ( %s ` i ) ) = %s )' % (A0, PSD, PSD))], 'eqtrd',
            '( %s -> ( i e. NN |-> ( CC _D ( %s ` i ) ) ) = %s )' % (A0, PS, PSD))
# its uniform limit
ulm = w.s([w.s([d['uh'], w.inst('uhdf')], 'syl', '( %s -> %s )' % (A0, UHSD)), w.inst('uhlim')], 'syl',
          '( %s -> %s ( ~~>u ` U ) %s )' % (A0, PSD, GD))
Azk = '( ( %s /\\ z e. U ) /\\ k e. NN )' % A0
dv3 = w.s([dfval(w, Azk, 'k', w.s([], 'simpr', '( %s -> k e. NN )' % Azk))], 'fveq1d',
          '( %s -> ( ( %s ` k ) ` z ) = ( ( CC _D ( F ` k ) ) ` z ) )' % (Azk, DFF))
sm = w.s([dv3], 'sumeq2dv', '( ( %s /\\ z e. U ) -> sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN ( ( CC _D ( F ` k ) ) ` z ) )' % (A0, DFF))
gdh = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A0, GD, H))
ulm2 = w.s([ulm, gdh], 'breqtrd', '( %s -> %s ( ~~>u ` U ) %s )' % (A0, PSD, H))
uu = w.s([ident, ulm2], 'eqbrtrd', '( %s -> ( i e. NN |-> ( CC _D ( %s ` i ) ) ) ( ~~>u ` U ) %s )' % (A0, PS, H))
w.qed([d['nu1'], sc, d['z1'], psf, gf, ptl, uu], 'ulmdv', '( %s -> ( CC _D %s ) = %s )' % (A0, G, H))
run5(w)

# ---------------------------------------------------------------- uhhol
w = W('uhhol', 'The sum of a holomorphic term-function sequence with summable majorants for '
      'the terms and their derivatives is holomorphic on the domain: Mathlib\'s '
      '` differentiableOn_tsum_of_summable_norm ` with an explicit derivative majorant.')
d = ctx(w, A0)
dveq = w.s([d['uh'], w.inst('uhdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, G, H))
Az = '( %s /\\ z e. U )' % A0
uhsd = w.s([w.s([d['uh']], 'adantr', '( %s -> %s )' % (Az, A0)), w.inst('uhdf')], 'syl', '( %s -> %s )' % (Az, UHSD))
cl0 = w.s([w.s([uhsd, w.s([], 'simpr', '( %s -> z e. U )' % Az)], 'jca', '( %s -> ( %s /\\ z e. U ) )' % (Az, UHSD)),
           w.inst('uhcl')], 'syl', '( %s -> sum_ k e. NN ( ( %s ` k ) ` z ) e. CC )' % (Az, DFF))
Azk = '( %s /\\ k e. NN )' % Az
dv3 = w.s([dfval(w, Azk, 'k', w.s([], 'simpr', '( %s -> k e. NN )' % Azk))], 'fveq1d',
          '( %s -> ( ( %s ` k ) ` z ) = ( ( CC _D ( F ` k ) ) ` z ) )' % (Azk, DFF))
sm = w.s([dv3], 'sumeq2dv', '( %s -> sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN ( ( CC _D ( F ` k ) ) ` z ) )' % (Az, DFF))
cls = w.s([sm, cl0], 'eqeltrrd', '( %s -> sum_ k e. NN ( ( CC _D ( F ` k ) ) ` z ) e. CC )' % Az)
RHS = 'sum_ k e. NN ( ( CC _D ( F ` k ) ) ` z )'
ssd = dvdom(w, A0, G, 'z', 'U', RHS, dveq, cls)
# continuity from the derivative
hf = w.s([cls, w.s([], 'eqid', '%s = %s' % (H, H))], 'fmptd', '( %s -> %s : U --> CC )' % (A0, H))
dm = w.s([w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, G, H)),
          w.s([hf, w.inst('fdm')], 'syl', '( %s -> dom %s = U )' % (A0, H))], 'eqtrd', '( %s -> dom ( CC _D %s ) = U )' % (A0, G))
gf = w.s([d['uhs'], w.inst('uhf')], 'syl', '( %s -> %s : U --> CC )' % (A0, G))
uo = uopn(w, A0, d)
ucc = opnss(w, A0, uo)
ccc = a1(w, A0, 'ssid', 'CC C_ CC')
cn = w.s([w.s([w.s([ccc, gf, ucc], '3jca', '( %s -> ( CC C_ CC /\\ %s : U --> CC /\\ U C_ CC ) )' % (A0, G)), dm], 'jca',
              '( %s -> ( ( CC C_ CC /\\ %s : U --> CC /\\ U C_ CC ) /\\ dom ( CC _D %s ) = U ) )' % (A0, G, G)), w.inst('dvcn')],
         'syl', '( %s -> %s e. ( U -cn-> CC ) )' % (A0, G))
w.qed([cn, ssd], 'jca', '( %s -> %s )' % (A0, HOLG2(G, 'U')))
run5(w)
