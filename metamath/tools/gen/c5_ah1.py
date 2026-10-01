"""C5, Abel holomorphy 1: the open box, holomorphy is local (holloc), the
log bound, and the Abel term functions' derivative and holomorphy."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

B = BX()
RE_ = '( `\' Re " ( L (,) R ) )'
IM_ = '( `\' Im " ( -u R (,) R ) )'
RZ = '( Re ` Z )'; IZ = '( Im ` Z )'
INB = '( Z e. CC /\\ ( L < %s /\\ %s < R ) /\\ ( -u R < %s /\\ %s < R ) )' % (RZ, RZ, IZ, IZ)

# ---------------------------------------------------------------- elbxi
w = W('elbxi', 'A point of the open box: it is complex, its real part lies strictly between the abscissae and '
      'its imaginary part strictly between minus and plus the height.')
A0 = 'Z e. %s' % B
both = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([], 'elin', '( Z e. %s <-> ( Z e. %s /\\ Z e. %s ) )' % (B, RE_, IM_))], 'sylib',
           '( %s -> ( Z e. %s /\\ Z e. %s ) )' % (A0, RE_, IM_))
refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
imfn = w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC')
pre1 = w.s([refn, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ %s e. ( L (,) R ) ) )' % (RE_, RZ))
pre2 = w.s([imfn, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ %s e. ( -u R (,) R ) ) )' % (IM_, IZ))
r1 = w.s([w.s([both], 'simpld', '( %s -> Z e. %s )' % (A0, RE_)), w.s([pre1], 'a1i', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ %s e. ( L (,) R ) ) ) )' % (A0, RE_, RZ))], 'mpbid',
         '( %s -> ( Z e. CC /\\ %s e. ( L (,) R ) ) )' % (A0, RZ))
i1 = w.s([w.s([both], 'simprd', '( %s -> Z e. %s )' % (A0, IM_)), w.s([pre2], 'a1i', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ %s e. ( -u R (,) R ) ) ) )' % (A0, IM_, IZ))], 'mpbid',
         '( %s -> ( Z e. CC /\\ %s e. ( -u R (,) R ) ) )' % (A0, IZ))
zc = w.s([r1], 'simpld', '( %s -> Z e. CC )' % A0)
rio = w.s([w.s([r1], 'simprd', '( %s -> %s e. ( L (,) R ) )' % (A0, RZ)), w.inst('eliooord')], 'syl', '( %s -> ( L < %s /\\ %s < R ) )' % (A0, RZ, RZ))
iio = w.s([w.s([i1], 'simprd', '( %s -> %s e. ( -u R (,) R ) )' % (A0, IZ)), w.inst('eliooord')], 'syl', '( %s -> ( -u R < %s /\\ %s < R ) )' % (A0, IZ, IZ))
w.qed([zc, rio, iio], '3jca', '( %s -> %s )' % (A0, INB))
run5(w)

# ---------------------------------------------------------------- elbxr
w = W('elbxr', 'A complex number with real part strictly between the abscissae and imaginary part strictly '
      'between minus and plus the height lies in the open box.')
A0 = '( ( L e. RR /\\ R e. RR ) /\\ %s )' % INB
lr = w.s([], 'simpll', '( %s -> L e. RR )' % A0)
rr = w.s([], 'simplr', '( %s -> R e. RR )' % A0)
inb = w.s([], 'simpr', '( %s -> %s )' % (A0, INB))
zc = w.s([inb, w.inst('simp1')], 'syl', '( %s -> Z e. CC )' % A0)
rio = w.s([inb, w.inst('simp2')], 'syl', '( %s -> ( L < %s /\\ %s < R ) )' % (A0, RZ, RZ))
iio = w.s([inb, w.inst('simp3')], 'syl', '( %s -> ( -u R < %s /\\ %s < R ) )' % (A0, IZ, IZ))
lx = w.s([lr], 'rexrd', '( %s -> L e. RR* )' % A0)
rx = w.s([rr], 'rexrd', '( %s -> R e. RR* )' % A0)
nrx = w.s([w.s([rr], 'renegcld', '( %s -> -u R e. RR )' % A0)], 'rexrd', '( %s -> -u R e. RR* )' % A0)
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
iz = w.s([zc], 'imcld', '( %s -> %s e. RR )' % (A0, IZ))
rin = w.s([w.s([rz, w.s([rio], 'simpld', '( %s -> L < %s )' % (A0, RZ)), w.s([rio], 'simprd', '( %s -> %s < R )' % (A0, RZ))], '3jca',
                '( %s -> ( %s e. RR /\\ L < %s /\\ %s < R ) )' % (A0, RZ, RZ, RZ)),
           w.s([lx, rx, w.inst('elioo2')], 'syl2anc', '( %s -> ( %s e. ( L (,) R ) <-> ( %s e. RR /\\ L < %s /\\ %s < R ) ) )' % (A0, RZ, RZ, RZ, RZ))], 'mpbird',
          '( %s -> %s e. ( L (,) R ) )' % (A0, RZ))
iin = w.s([w.s([iz, w.s([iio], 'simpld', '( %s -> -u R < %s )' % (A0, IZ)), w.s([iio], 'simprd', '( %s -> %s < R )' % (A0, IZ))], '3jca',
                '( %s -> ( %s e. RR /\\ -u R < %s /\\ %s < R ) )' % (A0, IZ, IZ, IZ)),
           w.s([nrx, rx, w.inst('elioo2')], 'syl2anc', '( %s -> ( %s e. ( -u R (,) R ) <-> ( %s e. RR /\\ -u R < %s /\\ %s < R ) ) )' % (A0, IZ, IZ, IZ, IZ))], 'mpbird',
          '( %s -> %s e. ( -u R (,) R ) )' % (A0, IZ))
refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
imfn = w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC')
pre1 = w.s([refn, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ %s e. ( L (,) R ) ) )' % (RE_, RZ))
pre2 = w.s([imfn, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ %s e. ( -u R (,) R ) ) )' % (IM_, IZ))
m1 = w.s([w.s([zc, rin], 'jca', '( %s -> ( Z e. CC /\\ %s e. ( L (,) R ) ) )' % (A0, RZ)), w.s([pre1], 'a1i', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ %s e. ( L (,) R ) ) ) )' % (A0, RE_, RZ))],
         'mpbird', '( %s -> Z e. %s )' % (A0, RE_))
m2 = w.s([w.s([zc, iin], 'jca', '( %s -> ( Z e. CC /\\ %s e. ( -u R (,) R ) ) )' % (A0, IZ)), w.s([pre2], 'a1i', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ %s e. ( -u R (,) R ) ) ) )' % (A0, IM_, IZ))],
         'mpbird', '( %s -> Z e. %s )' % (A0, IM_))
w.qed([m1, m2], 'elind', '( %s -> Z e. %s )' % (A0, B))
run5(w)

# ---------------------------------------------------------------- bxopn
w = W('bxopn', 'The open box is an open set of the complex plane ( ~ hpopn , ~ inopn ).')
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
kr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
lr = w.s([], 'tgioo4', '%s = ( %s |`t RR )' % (RETOP, TOP))
ce = w.s([ej, kr, lr], 'cncfcn', '( ( CC C_ CC /\\ RR C_ CC ) -> ( CC -cn-> RR ) = ( %s Cn %s ) )' % (TOP, RETOP))
ce2 = w.s([w.s([], 'ssid', 'CC C_ CC'), w.s([], 'ax-resscn', 'RR C_ CC'), ce], 'mp2an', '( CC -cn-> RR ) = ( %s Cn %s )' % (TOP, RETOP))
re2 = w.s([w.s([], 'recncf', 'Re e. ( CC -cn-> RR )'), ce2], 'eleqtri', 'Re e. ( %s Cn %s )' % (TOP, RETOP))
im2 = w.s([w.s([], 'imcncf', 'Im e. ( CC -cn-> RR )'), ce2], 'eleqtri', 'Im e. ( %s Cn %s )' % (TOP, RETOP))
o1 = w.s([re2, w.s([], 'iooretop', '( L (,) R ) e. %s' % RETOP), w.inst('cnima')], 'mp2an', '%s e. %s' % (RE_, TOP))
o2 = w.s([im2, w.s([], 'iooretop', '( -u R (,) R ) e. %s' % RETOP), w.inst('cnima')], 'mp2an', '%s e. %s' % (IM_, TOP))
tp = w.s([ej], 'cnfldtop', '%s e. Top' % TOP)
w.qed([tp, o1, o2, w.inst('inopn')], 'mp3an', '%s e. %s' % (B, TOP))
run5(w)

# ---------------------------------------------------------------- bxabs
w = W('bxabs', 'A point of an open box with nonnegative left abscissa has modulus at most twice the height.')
A0 = '( ( L e. RR /\\ 0 <_ L /\\ R e. RR ) /\\ Z e. %s )' % B
lr = w.s([], 'simpl1', '( %s -> L e. RR )' % A0)
l0 = w.s([], 'simpl2', '( %s -> 0 <_ L )' % A0)
rr = w.s([], 'simpl3', '( %s -> R e. RR )' % A0)
inb = w.s([w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, B)), w.inst('elbxi')], 'syl', '( %s -> %s )' % (A0, INB))
zc = w.s([inb, w.inst('simp1')], 'syl', '( %s -> Z e. CC )' % A0)
rio = w.s([inb, w.inst('simp2')], 'syl', '( %s -> ( L < %s /\\ %s < R ) )' % (A0, RZ, RZ))
iio = w.s([inb, w.inst('simp3')], 'syl', '( %s -> ( -u R < %s /\\ %s < R ) )' % (A0, IZ, IZ))
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
iz = w.s([zc], 'imcld', '( %s -> %s e. RR )' % (A0, IZ))
rzc = w.s([rz], 'recnd', '( %s -> %s e. CC )' % (A0, RZ))
izc = w.s([iz], 'recnd', '( %s -> %s e. CC )' % (A0, IZ))
ic = a1(w, A0, 'ax-icn', '_i e. CC')
iiz = w.s([ic, izc], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IZ))
rep = w.s([zc], 'replimd', '( %s -> Z = ( %s + ( _i x. %s ) ) )' % (A0, RZ, IZ))
tri = w.s([rzc, iiz, w.inst('abstri')], 'syl2anc', '( %s -> ( abs ` ( %s + ( _i x. %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( _i x. %s ) ) ) )' % (A0, RZ, IZ, RZ, IZ))
abiz = w.s([izc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, IZ))
aii = w.s([w.s([ic, izc], 'absmuld', '( %s -> ( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (A0, IZ, IZ)),
           w.s([w.s([a1(w, A0, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) ) )' % (A0, IZ, IZ)),
                w.s([w.s([abiz], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (A0, IZ))], 'mullidd', '( %s -> ( 1 x. ( abs ` %s ) ) = ( abs ` %s ) )' % (A0, IZ, IZ))], 'eqtrd',
               '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s ) )' % (A0, IZ, IZ))], 'eqtrd', '( %s -> ( abs ` ( _i x. %s ) ) = ( abs ` %s ) )' % (A0, IZ, IZ))
tri2 = w.s([w.s([w.s([rep], 'fveq2d', '( %s -> ( abs ` Z ) = ( abs ` ( %s + ( _i x. %s ) ) ) )' % (A0, RZ, IZ)), tri], 'eqbrtrd',
                '( %s -> ( abs ` Z ) <_ ( ( abs ` %s ) + ( abs ` ( _i x. %s ) ) ) )' % (A0, RZ, IZ)),
            w.s([aii], 'oveq2d', '( %s -> ( ( abs ` %s ) + ( abs ` ( _i x. %s ) ) ) = ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, RZ, IZ, RZ, IZ))], 'breqtrd',
           '( %s -> ( abs ` Z ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, RZ, IZ))
# |Re Z| <_ R and |Im Z| <_ R
rz0 = w.s([a1(w, A0, '0re', '0 e. RR'), lr, rz, l0, w.s([rio], 'simpld', '( %s -> L < %s )' % (A0, RZ))], 'lelttrd', '( %s -> 0 < %s )' % (A0, RZ))
rz0le = w.s([a1(w, A0, '0re', '0 e. RR'), rz, rz0], 'ltled', '( %s -> 0 <_ %s )' % (A0, RZ))
arz = w.s([rz, rz0le], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A0, RZ, RZ))
arzle = w.s([arz, w.s([rz, rr, w.s([rio], 'simprd', '( %s -> %s < R )' % (A0, RZ))], 'ltled', '( %s -> %s <_ R )' % (A0, RZ))], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ R )' % (A0, RZ))
aizlt = w.s([iio, w.s([iz, rr, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` %s ) < R <-> ( -u R < %s /\\ %s < R ) ) )' % (A0, IZ, IZ, IZ))], 'mpbird', '( %s -> ( abs ` %s ) < R )' % (A0, IZ))
aizle = w.s([abiz, rr, aizlt], 'ltled', '( %s -> ( abs ` %s ) <_ R )' % (A0, IZ))
arzr = w.s([rzc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, RZ))
sm = w.s([arzr, abiz, rr, rr, arzle, aizle], 'le2addd', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ ( R + R ) )' % (A0, RZ, IZ))
two = w.s([w.s([w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)], '2timesd', '( %s -> ( 2 x. R ) = ( R + R ) )' % A0)], 'eqcomd', '( %s -> ( R + R ) = ( 2 x. R ) )' % A0)
t1 = w.s([w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0), w.s([arzr, abiz], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A0, RZ, IZ)),
          w.s([rr, rr], 'readdcld', '( %s -> ( R + R ) e. RR )' % A0), tri2, sm], 'letrd', '( %s -> ( abs ` Z ) <_ ( R + R ) )' % A0)
w.qed([t1, two], 'breqtrd', '( %s -> ( abs ` Z ) <_ ( 2 x. R ) )' % A0)
run5(w)

# ---------------------------------------------------------------- holloc
w = W('holloc', 'Holomorphy is local: a function on a subset of the plane that is differentiable on an open '
      'neighbourhood of each point of its domain, with the derivative of the restriction defined on the whole '
      'neighbourhood, is holomorphic on its domain ( ~ dvres , ~ dvbss , ~ dvcn ).')


def LOC(y, u):
    return '( %s e. %s /\\ %s C_ D /\\ %s C_ dom ( CC _D ( G |` %s ) ) )' % (y, u, u, u, u)


QH = 'A. y e. D E. u e. %s %s' % (TOP, LOC('y', 'u'))
A0 = '( ( G : D --> CC /\\ D C_ CC ) /\\ %s )' % QH
gf = w.s([w.s([], 'simpl', '( %s -> ( G : D --> CC /\\ D C_ CC ) )' % A0), w.inst('simpl')], 'syl', '( %s -> G : D --> CC )' % A0)
dcc = w.s([w.s([], 'simpl', '( %s -> ( G : D --> CC /\\ D C_ CC ) )' % A0), w.inst('simpr')], 'syl', '( %s -> D C_ CC )' % A0)
qh = w.s([], 'simpr', '( %s -> %s )' % (A0, QH))
Aw = '( %s /\\ w e. D )' % A0
wd = w.s([], 'simpr', '( %s -> w e. D )' % Aw)
sb = w.s([w.s([w.s([], 'eleq1', '( y = w -> ( y e. u <-> w e. u ) )')], '3anbi1d', '( y = w -> ( %s <-> %s ) )' % (LOC('y', 'u'), LOC('w', 'u')))], 'rexbidv',
         '( y = w -> ( E. u e. %s %s <-> E. u e. %s %s ) )' % (TOP, LOC('y', 'u'), TOP, LOC('w', 'u')))
exu = w.s([sb, w.s([qh], 'adantr', '( %s -> %s )' % (Aw, QH)), wd], 'rspcdva', '( %s -> E. u e. %s %s )' % (Aw, TOP, LOC('w', 'u')))
sbv = w.s([w.s([], 'eleq2', '( u = v -> ( w e. u <-> w e. v ) )'), w.s([], 'sseq1', '( u = v -> ( u C_ D <-> v C_ D ) )'),
           w.s([w.s([], 'id', '( u = v -> u = v )'), w.s([w.s([w.s([], 'reseq2', '( u = v -> ( G |` u ) = ( G |` v ) )')], 'oveq2d', '( u = v -> ( CC _D ( G |` u ) ) = ( CC _D ( G |` v ) ) )')],
                                                        'dmeqd', '( u = v -> dom ( CC _D ( G |` u ) ) = dom ( CC _D ( G |` v ) ) )')], 'sseq12d',
               '( u = v -> ( u C_ dom ( CC _D ( G |` u ) ) <-> v C_ dom ( CC _D ( G |` v ) ) ) )')], '3anbi123d', '( u = v -> ( %s <-> %s ) )' % (LOC('w', 'u'), LOC('w', 'v')))
cbv = w.s([sbv], 'cbvrexvw', '( E. u e. %s %s <-> E. v e. %s %s )' % (TOP, LOC('w', 'u'), TOP, LOC('w', 'v')))
exv = w.s([exu, w.s([cbv], 'a1i', '( %s -> ( E. u e. %s %s <-> E. v e. %s %s ) )' % (Aw, TOP, LOC('w', 'u'), TOP, LOC('w', 'v')))], 'mpbid', '( %s -> E. v e. %s %s )' % (Aw, TOP, LOC('w', 'v')))
Av = '( ( %s /\\ v e. %s ) /\\ %s )' % (Aw, TOP, LOC('w', 'v'))
vo = w.s([], 'simplr', '( %s -> v e. %s )' % (Av, TOP))
loc = w.s([], 'simpr', '( %s -> %s )' % (Av, LOC('w', 'v')))
wv = w.s([loc, w.inst('simp1')], 'syl', '( %s -> w e. v )' % Av)
vss = w.s([loc, w.inst('simp3')], 'syl', '( %s -> v C_ dom ( CC _D ( G |` v ) ) )' % Av)
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
et = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
vcc = opnss(w, Av, vo, 'v')
dres = w.s([w.s([w.s([a1(w, Av, 'ssid', 'CC C_ CC'), w.s([gf], 'ad3antrrr', '( %s -> G : D --> CC )' % Av)], 'jca', '( %s -> ( CC C_ CC /\\ G : D --> CC ) )' % Av),
                 w.s([w.s([dcc], 'ad3antrrr', '( %s -> D C_ CC )' % Av), vcc], 'jca', '( %s -> ( D C_ CC /\\ v C_ CC ) )' % Av)], 'jca',
                '( %s -> ( ( CC C_ CC /\\ G : D --> CC ) /\\ ( D C_ CC /\\ v C_ CC ) ) )' % Av), w.s([ek, et], 'dvres',
                '( ( ( CC C_ CC /\\ G : D --> CC ) /\\ ( D C_ CC /\\ v C_ CC ) ) -> ( CC _D ( G |` v ) ) = ( ( CC _D G ) |` ( ( int ` %s ) ` v ) ) )' % TOP)], 'syl',
           '( %s -> ( CC _D ( G |` v ) ) = ( ( CC _D G ) |` ( ( int ` %s ) ` v ) ) )' % (Av, TOP))
_, tp = cnfldtop(w, Av)
ntr = w.s([tp, vo, w.inst('isopn3i')], 'syl2anc', '( %s -> ( ( int ` %s ) ` v ) = v )' % (Av, TOP))
dres2 = w.s([dres, w.s([ntr], 'reseq2d', '( %s -> ( ( CC _D G ) |` ( ( int ` %s ) ` v ) ) = ( ( CC _D G ) |` v ) )' % (Av, TOP))], 'eqtrd',
            '( %s -> ( CC _D ( G |` v ) ) = ( ( CC _D G ) |` v ) )' % Av)
dm = w.s([w.s([dres2], 'dmeqd', '( %s -> dom ( CC _D ( G |` v ) ) = dom ( ( CC _D G ) |` v ) )' % Av),
          a1(w, Av, 'dmres', 'dom ( ( CC _D G ) |` v ) = ( v i^i dom ( CC _D G ) )')], 'eqtrd', '( %s -> dom ( CC _D ( G |` v ) ) = ( v i^i dom ( CC _D G ) ) )' % Av)
vss2 = w.s([vss, dm], 'sseqtrd', '( %s -> v C_ ( v i^i dom ( CC _D G ) ) )' % Av)
win = w.s([vss2, wv], 'sseldd', '( %s -> w e. ( v i^i dom ( CC _D G ) ) )' % Av)
wdm = w.s([w.s([win, w.s([], 'elin', '( w e. ( v i^i dom ( CC _D G ) ) <-> ( w e. v /\\ w e. dom ( CC _D G ) ) )')], 'sylib', '( %s -> ( w e. v /\\ w e. dom ( CC _D G ) ) )' % Av)],
          'simprd', '( %s -> w e. dom ( CC _D G ) )' % Av)
imp = w.s([wdm], 'ex', '( ( %s /\\ v e. %s ) -> ( %s -> w e. dom ( CC _D G ) ) )' % (Aw, TOP, LOC('w', 'v')))
rex = w.s([imp], 'rexlimdva', '( %s -> ( E. v e. %s %s -> w e. dom ( CC _D G ) ) )' % (Aw, TOP, LOC('w', 'v')))
wdm2 = w.s([exv, rex], 'mpd', '( %s -> w e. dom ( CC _D G ) )' % Aw)
ss1 = w.s([w.s([wdm2], 'ex', '( %s -> ( w e. D -> w e. dom ( CC _D G ) ) )' % A0)], 'ssrdv', '( %s -> D C_ dom ( CC _D G ) )' % A0)
ss2 = w.s([a1(w, A0, 'ssid', 'CC C_ CC'), gf, dcc], 'dvbss', '( %s -> dom ( CC _D G ) C_ D )' % A0)
dme = w.s([ss2, ss1], 'eqssd', '( %s -> dom ( CC _D G ) = D )' % A0)
cn = w.s([w.s([w.s([a1(w, A0, 'ssid', 'CC C_ CC'), gf, dcc], '3jca', '( %s -> ( CC C_ CC /\\ G : D --> CC /\\ D C_ CC ) )' % A0), dme], 'jca',
              '( %s -> ( ( CC C_ CC /\\ G : D --> CC /\\ D C_ CC ) /\\ dom ( CC _D G ) = D ) )' % A0), w.inst('dvcn')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
w.qed([cn, ss1], 'jca', '( %s -> %s )' % (A0, HOLG2('G', 'D')))
run5(w)

# ---------------------------------------------------------------- logp1bnd
w = W('logp1bnd', 'The logarithm of ` K + 1 ` is bounded by a constant multiple of ` K ^c E ` for every '
      'positive ` E ` ( ~ logcxpbnd at ` 2 K ` ).')
A0 = '( K e. NN /\\ E e. RR+ )'
kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0)
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
k1 = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
k2 = w.s([a1(w, A0, '2nn', '2 e. NN'), kn, w.inst('nnmulcl')], 'syl2anc', '( %s -> ( 2 x. K ) e. NN )' % A0)
le = w.s([w.s([a1(w, A0, '1re', '1 e. RR'), kr, kr, w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)], 'leadd2dd', '( %s -> ( K + 1 ) <_ ( K + K ) )' % A0),
          w.s([w.s([kc], '2timesd', '( %s -> ( 2 x. K ) = ( K + K ) )' % A0)], 'eqcomd', '( %s -> ( K + K ) = ( 2 x. K ) )' % A0)], 'breqtrd', '( %s -> ( K + 1 ) <_ ( 2 x. K ) )' % A0)
lle = w.s([le, w.s([w.s([k1], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0), w.s([k2], 'nnrpd', '( %s -> ( 2 x. K ) e. RR+ )' % A0), w.inst('logleb')], 'syl2anc',
                   '( %s -> ( ( K + 1 ) <_ ( 2 x. K ) <-> ( log ` ( K + 1 ) ) <_ ( log ` ( 2 x. K ) ) ) )' % A0)], 'mpbid', '( %s -> ( log ` ( K + 1 ) ) <_ ( log ` ( 2 x. K ) ) )' % A0)
lb = w.s([k2, erp, w.inst('logcxpbnd')], 'syl2anc', '( %s -> ( log ` ( 2 x. K ) ) <_ ( ( ( 2 x. K ) ^c E ) / E ) )' % A0)
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
ec = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
k0 = w.s([w.s([kn], 'nnnn0d', '( %s -> K e. NN0 )' % A0)], 'nn0ge0d', '( %s -> 0 <_ K )' % A0)
mc = w.s([w.s([a1(w, A0, '2re', '2 e. RR'), a1(w, A0, '0le2', '0 <_ 2')], 'jca', '( %s -> ( 2 e. RR /\\ 0 <_ 2 ) )' % A0), w.s([kr, k0], 'jca', '( %s -> ( K e. RR /\\ 0 <_ K ) )' % A0), ec,
           w.inst('mulcxp')], 'syl3anc', '( %s -> ( ( 2 x. K ) ^c E ) = ( ( 2 ^c E ) x. ( K ^c E ) ) )' % A0)
c2e = w.s([w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), er], 'rpcxpcld', '( %s -> ( 2 ^c E ) e. RR+ )' % A0)], 'rpcnd', '( %s -> ( 2 ^c E ) e. CC )' % A0)], 'idi', '( %s -> ( 2 ^c E ) e. CC )' % A0)
cke = w.s([w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0), er], 'rpcxpcld', '( %s -> ( K ^c E ) e. RR+ )' % A0)], 'rpcnd', '( %s -> ( K ^c E ) e. CC )' % A0)
dv = w.s([c2e, cke, ec, w.s([erp], 'rpne0d', '( %s -> E =/= 0 )' % A0)], 'div23d', '( %s -> ( ( ( 2 ^c E ) x. ( K ^c E ) ) / E ) = ( ( ( 2 ^c E ) / E ) x. ( K ^c E ) ) )' % A0)
rhs = w.s([w.s([mc], 'oveq1d', '( %s -> ( ( ( 2 x. K ) ^c E ) / E ) = ( ( ( 2 ^c E ) x. ( K ^c E ) ) / E ) )' % A0), dv], 'eqtrd',
          '( %s -> ( ( ( 2 x. K ) ^c E ) / E ) = ( ( ( 2 ^c E ) / E ) x. ( K ^c E ) ) )' % A0)
l1r = w.s([w.s([k1], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` ( K + 1 ) ) e. RR )' % A0)
l2r = w.s([w.s([k2], 'nnrpd', '( %s -> ( 2 x. K ) e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` ( 2 x. K ) ) e. RR )' % A0)
qr = w.s([w.s([w.s([w.s([k2], 'nnrpd', '( %s -> ( 2 x. K ) e. RR+ )' % A0), er], 'rpcxpcld', '( %s -> ( ( 2 x. K ) ^c E ) e. RR+ )' % A0), erp], 'rpdivcld',
              '( %s -> ( ( ( 2 x. K ) ^c E ) / E ) e. RR+ )' % A0)], 'rpred', '( %s -> ( ( ( 2 x. K ) ^c E ) / E ) e. RR )' % A0)
w.qed([w.s([l1r, l2r, qr, lle, lb], 'letrd', '( %s -> ( log ` ( K + 1 ) ) <_ ( ( ( 2 x. K ) ^c E ) / E ) )' % A0), rhs], 'breqtrd',
      '( %s -> ( log ` ( K + 1 ) ) <_ ( ( ( 2 ^c E ) / E ) x. ( K ^c E ) ) )' % A0)
run5(w)

# ---------------------------------------------------------------- abtdv
w = W('abtdv', 'The derivative of an Abel term function on an open set ( ~ cxpnegdv , ~ dvmptsub , ~ dvmptcmul ).')
A0 = '( ( S : NN --> CC /\\ K e. NN ) /\\ U e. %s )' % TOP
sf = w.s([], 'simpll', '( %s -> S : NN --> CC )' % A0)
kn = w.s([], 'simplr', '( %s -> K e. NN )' % A0)
uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, TOP))
sk = w.s([sf, kn], 'ffvelcdmd', '( %s -> ( S ` K ) e. CC )' % A0)
k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
sc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
ucc = opnss(w, A0, uo)
Az = '( %s /\\ z e. U )' % A0
zc = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Az), w.s([], 'simpr', '( %s -> z e. U )' % Az)], 'sseldd', '( %s -> z e. CC )' % Az)
nz = w.s([zc], 'negcld', '( %s -> -u z e. CC )' % Az)
DK = '-u ( ( log ` K ) x. ( K ^c -u z ) )'; DK1 = '-u ( ( log ` ( K + 1 ) ) x. ( ( K + 1 ) ^c -u z ) )'
LK = '( ( log ` K ) x. ( K ^c -u z ) )'; LK1 = '( ( log ` ( K + 1 ) ) x. ( ( K + 1 ) ^c -u z ) )'


def cxpz(w, Kt, mk):
    kc = w.s([w.s([mk], 'nncnd', '( %s -> %s e. CC )' % (A0, Kt))], 'adantr', '( %s -> %s e. CC )' % (Az, Kt))
    pw = w.s([kc, nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( %s ^c -u z ) e. CC )' % (Az, Kt))
    lg = w.s([w.s([w.s([w.s([mk], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, Kt))], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (A0, Kt))], 'recnd',
                  '( %s -> ( log ` %s ) e. CC )' % (A0, Kt))], 'adantr', '( %s -> ( log ` %s ) e. CC )' % (Az, Kt))
    lpw = w.s([lg, pw], 'mulcld', '( %s -> ( ( log ` %s ) x. ( %s ^c -u z ) ) e. CC )' % (Az, Kt, Kt))
    dv = w.s([w.s([w.s([mk], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, Kt)), uo], 'jca', '( %s -> ( %s e. RR+ /\\ U e. %s ) )' % (A0, Kt, TOP)), w.inst('cxpnegdv')], 'syl',
             '( %s -> ( CC _D ( z e. U |-> ( %s ^c -u z ) ) ) = ( z e. U |-> -u ( ( log ` %s ) x. ( %s ^c -u z ) ) ) )' % (A0, Kt, Kt, Kt))
    return pw, lpw, w.s([lpw], 'negcld', '( %s -> -u ( ( log ` %s ) x. ( %s ^c -u z ) ) e. CC )' % (Az, Kt, Kt)), dv


pw, lpw, npw, dv = cxpz(w, 'K', kn)
pw1, lpw1, npw1, dv1 = cxpz(w, '( K + 1 )', k1n)
dsub = w.s([sc, pw, npw, dv, pw1, npw1, dv1], 'dvmptsub',
           '( %s -> ( CC _D ( z e. U |-> ( ( K ^c -u z ) - ( ( K + 1 ) ^c -u z ) ) ) ) = ( z e. U |-> ( %s - %s ) ) )' % (A0, DK, DK1))
dif = w.s([pw, pw1], 'subcld', '( %s -> ( ( K ^c -u z ) - ( ( K + 1 ) ^c -u z ) ) e. CC )' % Az)
ddif = w.s([npw, npw1], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (Az, DK, DK1))
dcm = w.s([sc, dif, ddif, dsub, sk], 'dvmptcmul', '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> ( ( S ` K ) x. ( %s - %s ) ) ) )' % (A0, ATM('S', 'K', 'z'), DK, DK1))
body = w.s([w.s([lpw, lpw1], 'neg2subd', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (Az, DK, DK1, LK1, LK))], 'oveq2d',
           '( %s -> ( ( S ` K ) x. ( %s - %s ) ) = %s )' % (Az, DK, DK1, DAT('S', 'K', 'z')))
w.qed([dcm, w.s([body], 'mpteq2dva', '( %s -> ( z e. U |-> ( ( S ` K ) x. ( %s - %s ) ) ) = ( z e. U |-> %s ) )' % (A0, DK, DK1, DAT('S', 'K', 'z')))], 'eqtrd',
      '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (A0, ATM('S', 'K', 'z'), DAT('S', 'K', 'z')))
run5(w)

# ---------------------------------------------------------------- abthol
w = W('abthol', 'An Abel term function is holomorphic on every open set.')
A0 = '( ( S : NN --> CC /\\ K e. NN ) /\\ U e. %s )' % TOP
MPK = '( z e. U |-> %s )' % ATM('S', 'K', 'z')
DB = DAT('S', 'K', 'z')
sf = w.s([], 'simpll', '( %s -> S : NN --> CC )' % A0)
kn = w.s([], 'simplr', '( %s -> K e. NN )' % A0)
uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, TOP))
sk = w.s([sf, kn], 'ffvelcdmd', '( %s -> ( S ` K ) e. CC )' % A0)
k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
ucc = opnss(w, A0, uo)
Az = '( %s /\\ z e. U )' % A0
zc = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Az), w.s([], 'simpr', '( %s -> z e. U )' % Az)], 'sseldd', '( %s -> z e. CC )' % Az)
nz = w.s([zc], 'negcld', '( %s -> -u z e. CC )' % Az)


def pieces(Kt, mk):
    kc = w.s([w.s([mk], 'nncnd', '( %s -> %s e. CC )' % (A0, Kt))], 'adantr', '( %s -> %s e. CC )' % (Az, Kt))
    pw = w.s([kc, nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( %s ^c -u z ) e. CC )' % (Az, Kt))
    lg = w.s([w.s([w.s([w.s([mk], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, Kt))], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (A0, Kt))], 'recnd',
                  '( %s -> ( log ` %s ) e. CC )' % (A0, Kt))], 'adantr', '( %s -> ( log ` %s ) e. CC )' % (Az, Kt))
    return pw, w.s([lg, pw], 'mulcld', '( %s -> ( ( log ` %s ) x. ( %s ^c -u z ) ) e. CC )' % (Az, Kt, Kt))


pw, lpw = pieces('K', kn)
pw1, lpw1 = pieces('( K + 1 )', k1n)
skz = w.s([sk], 'adantr', '( %s -> ( S ` K ) e. CC )' % Az)
tc = w.s([skz, w.s([pw, pw1], 'subcld', '( %s -> ( ( K ^c -u z ) - ( ( K + 1 ) ^c -u z ) ) e. CC )' % Az)], 'mulcld', '( %s -> %s e. CC )' % (Az, ATM('S', 'K', 'z')))
cls = w.s([skz, w.s([lpw1, lpw], 'subcld', '( %s -> ( ( ( log ` ( K + 1 ) ) x. ( ( K + 1 ) ^c -u z ) ) - ( ( log ` K ) x. ( K ^c -u z ) ) ) e. CC )' % Az)], 'mulcld',
          '( %s -> %s e. CC )' % (Az, DB))
dveq = w.s([], 'abtdv', '( %s -> ( CC _D %s ) = ( z e. U |-> %s ) )' % (A0, MPK, DB))
ssd = dvdom(w, A0, MPK, 'z', 'U', DB, dveq, cls)
hf = w.s([cls, w.s([], 'eqid', '( z e. U |-> %s ) = ( z e. U |-> %s )' % (DB, DB))], 'fmptd', '( %s -> ( z e. U |-> %s ) : U --> CC )' % (A0, DB))
dm = w.s([w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( z e. U |-> %s ) )' % (A0, MPK, DB)), w.s([hf, w.inst('fdm')], 'syl', '( %s -> dom ( z e. U |-> %s ) = U )' % (A0, DB))],
         'eqtrd', '( %s -> dom ( CC _D %s ) = U )' % (A0, MPK))
gf = w.s([tc, w.s([], 'eqid', '%s = %s' % (MPK, MPK))], 'fmptd', '( %s -> %s : U --> CC )' % (A0, MPK))
cn = w.s([w.s([w.s([a1(w, A0, 'ssid', 'CC C_ CC'), gf, ucc], '3jca', '( %s -> ( CC C_ CC /\\ %s : U --> CC /\\ U C_ CC ) )' % (A0, MPK)), dm], 'jca',
              '( %s -> ( ( CC C_ CC /\\ %s : U --> CC /\\ U C_ CC ) /\\ dom ( CC _D %s ) = U ) )' % (A0, MPK, MPK)), w.inst('dvcn')], 'syl', '( %s -> %s e. ( U -cn-> CC ) )' % (A0, MPK))
w.qed([cn, ssd], 'jca', '( %s -> %s )' % (A0, HOLG2(MPK, 'U')))
run5(w)
