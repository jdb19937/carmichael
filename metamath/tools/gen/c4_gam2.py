"""C4, Gamma block 2: Euler's product term and its modulus."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

RZ = '( Re ` Z )'
EZ = EUT('Z'); EX = EUT(RZ)
def BZ(M): return EUTB('Z', M)
def BX(M): return EUTB(RZ, M)
NUM = '( ( ( M + 1 ) / M ) ^c ( Re ` Z ) )'
DEN = '( ( Z / M ) + 1 )'
XDEN = '( ( ( Re ` Z ) / M ) + 1 )'

A0 = '( ( Z e. CC /\\ 0 < ( Re ` Z ) ) /\\ M e. NN )'


def ctx(w, A0, Zc='simpll', Z0='simplr', Mn='simpr'):
    d = {}
    d['zc'] = w.s([], Zc, '( %s -> Z e. CC )' % A0)
    d['rz0'] = w.s([], Z0, '( %s -> 0 < %s )' % (A0, RZ))
    d['mn'] = w.s([], Mn, '( %s -> M e. NN )' % A0)
    d['rzr'] = w.s([d['zc']], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    d['rzrp'] = w.s([d['rzr'], d['rz0']], 'elrpd', '( %s -> %s e. RR+ )' % (A0, RZ))
    d['mrp'] = w.s([d['mn']], 'nnrpd', '( %s -> M e. RR+ )' % A0)
    d['mr'] = w.s([d['mn']], 'nnred', '( %s -> M e. RR )' % A0)
    d['mc'] = w.s([d['mrp']], 'rpcnd', '( %s -> M e. CC )' % A0)
    d['mne'] = w.s([d['mrp']], 'rpne0d', '( %s -> M =/= 0 )' % A0)
    one = w.s([], '1rp', '1 e. RR+')
    d['1rp'] = w.s([one], 'a1i', '( %s -> 1 e. RR+ )' % A0)
    d['m1rp'] = w.s([d['mrp'], d['1rp']], 'rpaddcld', '( %s -> ( M + 1 ) e. RR+ )' % A0)
    d['qrp'] = w.s([d['m1rp'], d['mrp']], 'rpdivcld', '( %s -> ( ( M + 1 ) / M ) e. RR+ )' % A0)
    d['num'] = w.s([d['qrp'], d['rzr']], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, NUM))
    d['zdm'] = w.s([d['zc'], d['mc'], d['mne']], 'divcld', '( %s -> ( Z / M ) e. CC )' % A0)
    one_c = w.s([], 'ax-1cn', '1 e. CC')
    d['den'] = w.s([d['zdm'], w.s([one_c], 'a1i', '( %s -> 1 e. CC )' % A0)], 'addcld',
                   '( %s -> %s e. CC )' % (A0, DEN))
    # Re ( ( Z / M ) + 1 ) = ( ( Re ` Z ) / M ) + 1
    r1 = w.s([d['zdm'], w.s([one_c], 'a1i', '( %s -> 1 e. CC )' % A0)], 'readdd',
             '( %s -> ( Re ` %s ) = ( ( Re ` ( Z / M ) ) + ( Re ` 1 ) ) )' % (A0, DEN))
    r2 = w.s([d['mr'], d['mne'], d['zc']], 'redivd', '( %s -> ( Re ` ( Z / M ) ) = ( %s / M ) )' % (A0, RZ))
    re1 = w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A0)
    d['redenv'] = w.s([r1, w.s([r2, re1], 'oveq12d',
                               '( %s -> ( ( Re ` ( Z / M ) ) + ( Re ` 1 ) ) = %s )' % (A0, XDEN))],
                      'eqtrd', '( %s -> ( Re ` %s ) = %s )' % (A0, DEN, XDEN))
    d['xdrp'] = w.s([w.s([d['rzrp'], d['mrp']], 'rpdivcld', '( %s -> ( %s / M ) e. RR+ )' % (A0, RZ)),
                     d['1rp']], 'rpaddcld', '( %s -> %s e. RR+ )' % (A0, XDEN))
    # ( ( Z / M ) + 1 ) =/= 0 : its real part is positive
    z0 = w.s([], 're0', '( Re ` 0 ) = 0')
    ne = w.s([d['redenv'], w.s([d['xdrp']], 'rpgt0d', '( %s -> 0 < %s )' % (A0, XDEN))],
             'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, DEN))
    d['renep'] = ne
    # if DEN = 0 then Re DEN = 0, contradiction
    ps = '( %s /\\ %s = 0 )' % (A0, DEN)
    e1 = w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (ps, DEN))], 'fveq2d',
             '( %s -> ( Re ` %s ) = ( Re ` 0 ) )' % (ps, DEN))
    e2 = w.s([e1, w.s([z0], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % ps)], 'eqtrd',
             '( %s -> ( Re ` %s ) = 0 )' % (ps, DEN))
    e3 = w.s([ne], 'adantr', '( %s -> 0 < ( Re ` %s ) )' % (ps, DEN))
    e4 = w.s([e3, e2], 'breqtrd', '( %s -> 0 < 0 )' % ps)
    e5 = w.s([w.s([], '0re', '0 e. RR'), w.inst('ltnr')], 'ax-mp', '-. 0 < 0')
    d['denne'] = w.s([e4, w.s([e5], 'a1i', '( %s -> -. 0 < 0 )' % ps)], 'pm2.65da',
                     '( %s -> -. %s = 0 )' % (A0, DEN))
    d['denne'] = w.s([d['denne']], 'neqned', '( %s -> %s =/= 0 )' % (A0, DEN))
    d['absden'] = w.s([d['den'], d['denne']], 'absrpcld', '( %s -> ( abs ` %s ) e. RR+ )' % (A0, DEN))
    return d


# ---------------------------------------------------------------- eutval
w = W('eutval', 'The value of the ` M ` th term of Euler\'s product for the gamma '
      'function ( ~ gamcvg2 ).')
l1 = w.s([], 'id', '( m = M -> m = M )')
c, body = w.congr(EUTB('Z', 'm'), {'m': 'M'}, 'm = M', {'m': l1})
assert body == BZ('M'), body
em = w.s([], 'eqid', '%s = %s' % (EZ, EZ))
fv = w.s([c, em], 'fvmptg', '( ( M e. NN /\\ %s e. _V ) -> ( %s ` M ) = %s )' % (BZ('M'), EZ, BZ('M')))
ex = w.s([w.s([], 'ovex', '%s e. _V' % BZ('M'))], 'a1i', '( M e. NN -> %s e. _V )' % BZ('M'))
w.qed([w.s([], 'id', '( M e. NN -> M e. NN )'), ex, fv], 'syl2anc',
      '( M e. NN -> ( %s ` M ) = %s )' % (EZ, BZ('M')))
run4(w)

# ---------------------------------------------------------------- eutabs
w = W('eutabs', 'The modulus of the ` M ` th term of Euler\'s product ( ~ eutval ) '
      'at a complex argument: the numerator becomes the real power at the real part '
      '( ~ abscxp ).')
d = ctx(w, A0)
NUMZ = '( ( ( M + 1 ) / M ) ^c Z )'
v = w.s([d['mn'], w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = %s )' % (A0, EZ, BZ('M')))
va = w.s([v], 'fveq2d', '( %s -> ( abs ` ( %s ` M ) ) = ( abs ` %s ) )' % (A0, EZ, BZ('M')))
nz = w.s([w.s([d['qrp']], 'rpcnd', '( %s -> ( ( M + 1 ) / M ) e. CC )' % A0), d['zc']],
         'cxpcld', '( %s -> %s e. CC )' % (A0, NUMZ))
ad = w.s([nz, d['den'], d['denne']],
         'absdivd', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) ) )' % (A0, BZ('M'), NUMZ, DEN))
ac = w.s([d['qrp'], d['zc'], w.inst('abscxp')], 'syl2anc',
         '( %s -> ( abs ` %s ) = %s )' % (A0, NUMZ, NUM))
w.qed([va, w.s([ad, w.s([ac], 'oveq1d',
                        '( %s -> ( ( abs ` %s ) / ( abs ` %s ) ) = ( %s / ( abs ` %s ) ) )' % (A0, NUMZ, DEN, NUM, DEN))],
               'eqtrd', '( %s -> ( abs ` %s ) = ( %s / ( abs ` %s ) ) )' % (A0, BZ('M'), NUM, DEN))],
      'eqtrd', '( %s -> ( abs ` ( %s ` M ) ) = ( %s / ( abs ` %s ) ) )' % (A0, EZ, NUM, DEN))
run4(w)

# ---------------------------------------------------------------- eutxrp
w = W('eutxrp', 'The ` M ` th term of Euler\'s product ( ~ eutval ) at a positive '
      'real argument is a positive real.')
d = ctx(w, A0)
v = w.s([d['mn'], w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = %s )' % (A0, EX, BX('M')))
q = w.s([d['num'], d['xdrp']], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, BX('M')))
w.qed([v, q], 'eqeltrd', '( %s -> ( %s ` M ) e. RR+ )' % (A0, EX))
run4(w)

# ---------------------------------------------------------------- eutdlb
w = W('eutdlb', 'The denominator of Euler\'s term has modulus at least its real part.')
d = ctx(w, A0)
r = w.s([d['den'], w.inst('releabs')], 'syl', '( %s -> ( Re ` %s ) <_ ( abs ` %s ) )' % (A0, DEN, DEN))
w.qed([r, d['redenv']], 'eqbrtrrd', '( %s -> %s <_ ( abs ` %s ) )' % (A0, XDEN, DEN))
run4(w)

# ---------------------------------------------------------------- eutdlb2
w = W('eutdlb2', 'The denominator of Euler\'s term has modulus at least the height '
      'of the argument divided by the index.')
d = ctx(w, A0)
IMV = '( ( abs ` ( Im ` Z ) ) / M )'
i1 = w.s([d['mr'], d['mne'], d['zc']], 'imdivd', '( %s -> ( Im ` ( Z / M ) ) = ( ( Im ` Z ) / M ) )' % A0)
one_c = w.s([], 'ax-1cn', '1 e. CC')
i2 = w.s([d['zdm'], w.s([one_c], 'a1i', '( %s -> 1 e. CC )' % A0)], 'imaddd',
         '( %s -> ( Im ` %s ) = ( ( Im ` ( Z / M ) ) + ( Im ` 1 ) ) )' % (A0, DEN))
im1 = w.s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'a1i', '( %s -> ( Im ` 1 ) = 0 )' % A0)
i3 = w.s([i1, im1], 'oveq12d', '( %s -> ( ( Im ` ( Z / M ) ) + ( Im ` 1 ) ) = ( ( ( Im ` Z ) / M ) + 0 ) )' % A0)
imz = w.s([d['zc']], 'imcld', '( %s -> ( Im ` Z ) e. RR )' % A0)
i4 = w.s([w.s([imz, d['mr'], d['mne']], 'redivcld', '( %s -> ( ( Im ` Z ) / M ) e. RR )' % A0)], 'recnd',
         '( %s -> ( ( Im ` Z ) / M ) e. CC )' % A0)
i5 = w.s([i4], 'addridd', '( %s -> ( ( ( Im ` Z ) / M ) + 0 ) = ( ( Im ` Z ) / M ) )' % A0)
imd = w.s([i2, w.s([i3, i5], 'eqtrd',
                   '( %s -> ( ( Im ` ( Z / M ) ) + ( Im ` 1 ) ) = ( ( Im ` Z ) / M ) )' % A0)],
          'eqtrd', '( %s -> ( Im ` %s ) = ( ( Im ` Z ) / M ) )' % (A0, DEN))
a1 = w.s([d['den'], w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` %s ) ) <_ ( abs ` %s ) )' % (A0, DEN, DEN))
a2 = w.s([imd], 'fveq2d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` ( ( Im ` Z ) / M ) ) )' % (A0, DEN))
a3 = w.s([w.s([imz], 'recnd', '( %s -> ( Im ` Z ) e. CC )' % A0), d['mc'], d['mne']], 'absdivd',
         '( %s -> ( abs ` ( ( Im ` Z ) / M ) ) = ( ( abs ` ( Im ` Z ) ) / ( abs ` M ) ) )' % A0)
a4 = w.s([d['mr'], w.s([d['mrp']], 'rpge0d', '( %s -> 0 <_ M )' % A0)], 'absidd', '( %s -> ( abs ` M ) = M )' % A0)
a5 = w.s([a3, w.s([a4], 'oveq2d', '( %s -> ( ( abs ` ( Im ` Z ) ) / ( abs ` M ) ) = %s )' % (A0, IMV))],
         'eqtrd', '( %s -> ( abs ` ( ( Im ` Z ) / M ) ) = %s )' % (A0, IMV))
w.qed([a1, w.s([a2, a5], 'eqtrd', '( %s -> ( abs ` ( Im ` %s ) ) = %s )' % (A0, DEN, IMV))],
      'eqbrtrrd', '( %s -> %s <_ ( abs ` %s ) )' % (A0, IMV, DEN))
run4(w)

# ---------------------------------------------------------------- eutlev
w = W('eutlev', 'The modulus of Euler\'s term at a complex argument is at most its '
      'value at the real part: the denominator can only grow.')
d = ctx(w, A0)
ab = w.s([d['mn'], d['zc'], d['rz0']], 'eutabs', 'dummy')
w.lines.pop()
ab = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('eutabs')], 'syl',
         '( %s -> ( abs ` ( %s ` M ) ) = ( %s / ( abs ` %s ) ) )' % (A0, EZ, NUM, DEN))
vx = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('eutval')], 'mpdummy', 'x')
w.lines.pop()
vx = w.s([d['mn'], w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = %s )' % (A0, EX, BX('M')))
lb = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('eutdlb')], 'syl',
         '( %s -> %s <_ ( abs ` %s ) )' % (A0, XDEN, DEN))
le = w.s([d['xdrp'], d['absden'], w.s([d['num']], 'rpred', '( %s -> %s e. RR )' % (A0, NUM)),
          w.s([d['num']], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, NUM)), lb], 'lediv2ad',
         '( %s -> ( %s / ( abs ` %s ) ) <_ ( %s / %s ) )' % (A0, NUM, DEN, NUM, XDEN))
w.qed([w.s([le, w.s([vx], 'eqcomd', '( %s -> %s = ( %s ` M ) )' % (A0, BX('M'), EX))], 'breqtrd',
           '( %s -> ( %s / ( abs ` %s ) ) <_ ( %s ` M ) )' % (A0, NUM, DEN, EX)), ab],
      'eqbrtrrd' if False else 'jca', 'dummy')
w.lines.pop()
w.qed([ab, w.s([le, w.s([vx], 'eqcomd', '( %s -> %s = ( %s ` M ) )' % (A0, BX('M'), EX))], 'breqtrd',
               '( %s -> ( %s / ( abs ` %s ) ) <_ ( %s ` M ) )' % (A0, NUM, DEN, EX))],
      'eqbrtrd', '( %s -> ( abs ` ( %s ` M ) ) <_ ( %s ` M ) )' % (A0, EZ, EX))
run4(w)

# ---------------------------------------------------------------- eutlehv
A1 = '( %s /\\ ( 2 x. ( %s + M ) ) <_ ( abs ` ( Im ` Z ) ) )' % (A0, RZ)
w = W('eutlehv', 'Where the height of the argument is at least twice the real part '
      'plus the index, Euler\'s term at that index loses a factor of two.')
d = ctx(w, A1, Zc='simplll', Z0='simpllr', Mn='simplr')
hyp = w.s([], 'simpr', '( %s -> ( 2 x. ( %s + M ) ) <_ ( abs ` ( Im ` Z ) ) )' % (A1, RZ))
A0s = w.s([], 'simpl', '( %s -> %s )' % (A1, A0))
ab = w.s([A0s, w.inst('eutabs')], 'syl',
         '( %s -> ( abs ` ( %s ` M ) ) = ( %s / ( abs ` %s ) ) )' % (A1, EZ, NUM, DEN))
vx = w.s([d['mn'], w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = %s )' % (A1, EX, BX('M')))
lb2 = w.s([A0s, w.inst('eutdlb2')], 'syl',
          '( %s -> ( ( abs ` ( Im ` Z ) ) / M ) <_ ( abs ` %s ) )' % (A1, DEN))
# ( XDEN x. 2 ) = ( ( 2 x. ( X + M ) ) / M )
rzc = w.s([d['rzr']], 'recnd', '( %s -> %s e. CC )' % (A1, RZ))
sm = w.s([rzc, d['mc']], 'addcld', '( %s -> ( %s + M ) e. CC )' % (A1, RZ))
q1 = w.s([rzc, d['mc'], d['mc'], d['mne']], 'divdird',
         '( %s -> ( ( %s + M ) / M ) = ( ( %s / M ) + ( M / M ) ) )' % (A1, RZ, RZ))
q1b = w.s([d['mc'], d['mne']], 'dividd', '( %s -> ( M / M ) = 1 )' % A1)
q1c = w.s([q1, w.s([q1b], 'oveq2d', '( %s -> ( ( %s / M ) + ( M / M ) ) = %s )' % (A1, RZ, XDEN))],
          'eqtrd', '( %s -> ( ( %s + M ) / M ) = %s )' % (A1, RZ, XDEN))
two = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A1)
q2 = w.s([sm, two, d['mc'], d['mne']], 'div23d',
         '( %s -> ( ( ( %s + M ) x. 2 ) / M ) = ( ( ( %s + M ) / M ) x. 2 ) )' % (A1, RZ, RZ))
q3 = w.s([sm, two], 'mulcomd', '( %s -> ( ( %s + M ) x. 2 ) = ( 2 x. ( %s + M ) ) )' % (A1, RZ, RZ))
q4 = w.s([w.s([q3], 'oveq1d', '( %s -> ( ( ( %s + M ) x. 2 ) / M ) = ( ( 2 x. ( %s + M ) ) / M ) )' % (A1, RZ, RZ)),
          w.s([q2, w.s([q1c], 'oveq1d', '( %s -> ( ( ( %s + M ) / M ) x. 2 ) = ( %s x. 2 ) )' % (A1, RZ, XDEN))],
              'eqtrd', '( %s -> ( ( ( %s + M ) x. 2 ) / M ) = ( %s x. 2 ) )' % (A1, RZ, XDEN))],
         'eqtr3d', '( %s -> ( ( 2 x. ( %s + M ) ) / M ) = ( %s x. 2 ) )' % (A1, RZ, XDEN))
# ( 2 x. ( X + M ) ) / M <_ V / M
smr = w.s([d['rzr'], d['mr']], 'readdcld', '( %s -> ( %s + M ) e. RR )' % (A1, RZ))
t2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A1)
lhs = w.s([t2, smr], 'remulcld', '( %s -> ( 2 x. ( %s + M ) ) e. RR )' % (A1, RZ))
vr = w.s([w.s([d['zc']], 'imcld', '( %s -> ( Im ` Z ) e. RR )' % A1)], 'recnd', '( %s -> ( Im ` Z ) e. CC )' % A1)
vabs = w.s([vr], 'abscld', '( %s -> ( abs ` ( Im ` Z ) ) e. RR )' % A1)
dv = w.s([lhs, vabs, d['mrp'], hyp], 'lediv1dd',
         '( %s -> ( ( 2 x. ( %s + M ) ) / M ) <_ ( ( abs ` ( Im ` Z ) ) / M ) )' % (A1, RZ))
x2 = w.s([d['xdrp'], w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A1)], 'rpmulcld',
         '( %s -> ( %s x. 2 ) e. RR+ )' % (A1, XDEN))
x2r = w.s([x2], 'rpred', '( %s -> ( %s x. 2 ) e. RR )' % (A1, XDEN))
vmr = w.s([vabs, d['mr'], d['mne']], 'redivcld', '( %s -> ( ( abs ` ( Im ` Z ) ) / M ) e. RR )' % A1)
adr = w.s([d['absden']], 'rpred', '( %s -> ( abs ` %s ) e. RR )' % (A1, DEN))
key = w.s([x2r, vmr, adr,
           w.s([dv, q4], 'eqbrtrrd', '( %s -> ( %s x. 2 ) <_ ( ( abs ` ( Im ` Z ) ) / M ) )' % (A1, XDEN)),
           lb2], 'letrd', '( %s -> ( %s x. 2 ) <_ ( abs ` %s ) )' % (A1, XDEN, DEN))
le = w.s([x2, d['absden'], w.s([d['num']], 'rpred', '( %s -> %s e. RR )' % (A1, NUM)),
          w.s([d['num']], 'rpge0d', '( %s -> 0 <_ %s )' % (A1, NUM)), key], 'lediv2ad',
         '( %s -> ( %s / ( abs ` %s ) ) <_ ( %s / ( %s x. 2 ) ) )' % (A1, NUM, DEN, NUM, XDEN))
dd = w.s([w.s([d['num']], 'rpcnd', '( %s -> %s e. CC )' % (A1, NUM)),
          w.s([d['xdrp']], 'rpcnd', '( %s -> %s e. CC )' % (A1, XDEN)),
          w.s([d['xdrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A1, XDEN)), two,
          w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % A1)], 'divdiv1d',
         '( %s -> ( ( %s / %s ) / 2 ) = ( %s / ( %s x. 2 ) ) )' % (A1, NUM, XDEN, NUM, XDEN))
w.qed([ab, w.s([le, w.s([w.s([vx], 'oveq1d', '( %s -> ( ( %s ` M ) / 2 ) = ( %s / 2 ) )' % (A1, EX, BX('M'))),
                         dd], 'eqtrd', '( %s -> ( ( %s ` M ) / 2 ) = ( %s / ( %s x. 2 ) ) )' % (A1, EX, NUM, XDEN))],
               'breqtrrd', '( %s -> ( %s / ( abs ` %s ) ) <_ ( ( %s ` M ) / 2 ) )' % (A1, NUM, DEN, EX))],
      'eqbrtrd', '( %s -> ( abs ` ( %s ` M ) ) <_ ( ( %s ` M ) / 2 ) )' % (A1, EZ, EX))
run4(w)

# ---------------------------------------------------------------- eutzrp
w = W('eutzrp', 'The modulus of Euler\'s term at a complex argument with positive '
      'real part is a positive real.')
d = ctx(w, A0)
ab = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('eutabs')], 'syl',
         '( %s -> ( abs ` ( %s ` M ) ) = ( %s / ( abs ` %s ) ) )' % (A0, EZ, NUM, DEN))
q = w.s([d['num'], d['absden']], 'rpdivcld', '( %s -> ( %s / ( abs ` %s ) ) e. RR+ )' % (A0, NUM, DEN))
w.qed([ab, q], 'eqeltrd', '( %s -> ( abs ` ( %s ` M ) ) e. RR+ )' % (A0, EZ))
run4(w)

# ---------------------------------------------------------------- eutzcl
w = W('eutzcl', 'Euler\'s term at a complex argument with positive real part is a '
      'complex number.')
d = ctx(w, A0)
v = w.s([d['mn'], w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = %s )' % (A0, EZ, BZ('M')))
NUMZ = '( ( ( M + 1 ) / M ) ^c Z )'
nz = w.s([w.s([d['qrp']], 'rpcnd', '( %s -> ( ( M + 1 ) / M ) e. CC )' % A0), d['zc']],
         'cxpcld', '( %s -> %s e. CC )' % (A0, NUMZ))
q = w.s([nz, d['den'], d['denne']], 'divcld', '( %s -> %s e. CC )' % (A0, BZ('M')))
w.qed([v, q], 'eqeltrd', '( %s -> ( %s ` M ) e. CC )' % (A0, EZ))
run4(w)
