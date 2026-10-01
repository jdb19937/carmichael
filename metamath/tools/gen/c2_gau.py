"""Sortie C2 section 3.1c: the Gaussian normaliser exp ( E ( z ^ 2 - Q ) )."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

ARG = '( E x. ( ( z ^ 2 ) - Q ) )'
GAU = MP('z', '%s', '( exp ` %s )' % ARG)


def G(X):
    return MP('z', X, '( exp ` %s )' % ARG)


def cnel(w, A0):
    return w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)


# ---- gaucn -----------------------------------------------------------------
w = W('gaucn', 'The Gaussian normaliser is continuous on any set of complex numbers.')
A0 = '( E e. CC /\\ Q e. CC /\\ S C_ CC )'
ec = w.s([], 'simp1', '( %s -> E e. CC )' % A0)
qc = w.s([], 'simp2', '( %s -> Q e. CC )' % A0)
scc = w.s([], 'simp3', '( %s -> S C_ CC )' % A0)
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
idm = w.s([scc, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), w.inst('cncfmptid')], 'syl2anc', '( %s -> %s e. ( S -cn-> CC ) )' % (A0, MP('z', 'S', 'z')))
n02 = w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A0)
sqm = w.s([idm, n02, w.inst('cncfexpb')], 'syl2anc', '( %s -> %s e. ( S -cn-> CC ) )' % (A0, MP('z', 'S', '( z ^ 2 )')))
qm = w.s([qc, scc, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), w.inst('cncfmptc')], 'syl3anc',
         '( %s -> %s e. ( S -cn-> CC ) )' % (A0, MP('z', 'S', 'Q')))
scn = w.s([w.s([ej], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
dif = w.s([ej, scn, sqm, qm], 'cncfmpt2f', '( %s -> %s e. ( S -cn-> CC ) )' % (A0, MP('z', 'S', '( ( z ^ 2 ) - Q )')))
em = w.s([ec, scc, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), w.inst('cncfmptc')], 'syl3anc',
         '( %s -> %s e. ( S -cn-> CC ) )' % (A0, MP('z', 'S', 'E')))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
arg = w.s([ej, mcn, em, dif], 'cncfmpt2f', '( %s -> %s e. ( S -cn-> CC ) )' % (A0, MP('z', 'S', ARG)))
efm = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC')], 'a1i', '( %s -> exp : CC --> CC )' % A0)], 'feqmptd', '( %s -> exp = %s )' % (A0, MP('y', 'CC', '( exp ` y )')))
efc = w.s([efm, w.s([w.s([], 'efcn', 'exp e. ( CC -cn-> CC )')], 'a1i', '( %s -> exp e. ( CC -cn-> CC ) )' % A0)],
          'eqeltrrd', '( %s -> %s e. ( CC -cn-> CC ) )' % (A0, MP('y', 'CC', '( exp ` y )')))
nfz = w.s([], 'nfv', 'F/ z %s' % A0)
ccss = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
sty = w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = ( exp ` %s ) )' % (ARG, ARG))
w.qed([nfz, arg, efc, ccss, sty], 'cncfcompt2', '( %s -> %s e. ( S -cn-> CC ) )' % (A0, G('S'))); run1(w)

# ---- dvgau -----------------------------------------------------------------
w = W('dvgau', 'The derivative of the Gaussian normaliser on the whole plane.')
A0 = '( E e. CC /\\ Q e. CC )'
A1 = '( %s /\\ z e. CC )' % A0
A2 = '( %s /\\ y e. CC )' % A0
ec = w.s([], 'simpl', '( %s -> E e. CC )' % A0)
qc = w.s([], 'simpr', '( %s -> Q e. CC )' % A0)
ce = cnel(w, A0)
zc = w.s([], 'simpr', '( %s -> z e. CC )' % A1)
# d/dz z^2 = 2 z
dex = w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % A0), w.inst('dvexp')], 'syl',
          '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', '( z ^ 2 )'), MP('z', 'CC', '( 2 x. ( z ^ ( 2 - 1 ) ) )')))
e21 = w.s([w.s([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( %s -> ( 2 - 1 ) = 1 )' % A1)], 'oveq2d',
          '( %s -> ( z ^ ( 2 - 1 ) ) = ( z ^ 1 ) )' % A1)
e1z = w.s([e21, w.s([zc, w.inst('exp1')], 'syl', '( %s -> ( z ^ 1 ) = z )' % A1)], 'eqtrd', '( %s -> ( z ^ ( 2 - 1 ) ) = z )' % A1)
dsq = w.s([dex, w.s([w.s([e1z], 'oveq2d', '( %s -> ( 2 x. ( z ^ ( 2 - 1 ) ) ) = ( 2 x. z ) )' % A1)], 'mpteq2dva',
                    '( %s -> %s = %s )' % (A0, MP('z', 'CC', '( 2 x. ( z ^ ( 2 - 1 ) ) )'), MP('z', 'CC', '( 2 x. z )')))],
          'eqtrd', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', '( z ^ 2 )'), MP('z', 'CC', '( 2 x. z )')))
# d/dz ( z^2 - Q ) = 2 z
sqc = w.s([zc], 'sqcld', '( %s -> ( z ^ 2 ) e. CC )' % A1)
t2z = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A1), zc], 'mulcld', '( %s -> ( 2 x. z ) e. CC )' % A1)
qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
z0 = w.s([w.s([], '0cnd', '( %s -> 0 e. CC )' % A1)], 'idi', '( %s -> 0 e. CC )' % A1)
dqc = w.s([ce, qc, w.inst('dvmptc')], 'syl2anc', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', 'Q'), MP('z', 'CC', '0')))
dsub = w.s([ce, sqc, t2z, dsq, qc1, z0, dqc], 'dvmptsub',
           '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', '( ( z ^ 2 ) - Q )'), MP('z', 'CC', '( ( 2 x. z ) - 0 )')))
dsub2 = w.s([dsub, w.s([w.s([t2z], 'subid1d', '( %s -> ( ( 2 x. z ) - 0 ) = ( 2 x. z ) )' % A1)], 'mpteq2dva',
                       '( %s -> %s = %s )' % (A0, MP('z', 'CC', '( ( 2 x. z ) - 0 )'), MP('z', 'CC', '( 2 x. z )')))],
            'eqtrd', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', '( ( z ^ 2 ) - Q )'), MP('z', 'CC', '( 2 x. z )')))
sqq = w.s([sqc, qc1], 'subcld', '( %s -> ( ( z ^ 2 ) - Q ) e. CC )' % A1)
dcm = w.s([ce, sqq, t2z, dsub2, ec], 'dvmptcmul',
          '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', ARG), MP('z', 'CC', '( E x. ( 2 x. z ) )')))
# compose with exp
ec1 = w.s([ec], 'adantr', '( %s -> E e. CC )' % A1)
argc = w.s([ec1, sqq], 'mulcld', '( %s -> %s e. CC )' % (A1, ARG))
et2z = w.s([ec1, t2z], 'mulcld', '( %s -> ( E x. ( 2 x. z ) ) e. CC )' % A1)
yc = w.s([], 'simpr', '( %s -> y e. CC )' % A2)
eyc = w.s([yc, w.inst('efcl')], 'syl', '( %s -> ( exp ` y ) e. CC )' % A2)
efm = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC')], 'a1i', '( %s -> exp : CC --> CC )' % A0)], 'feqmptd', '( %s -> exp = %s )' % (A0, MP('y', 'CC', '( exp ` y )')))
dvefd = w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'a1i', '( %s -> ( CC _D exp ) = exp )' % A0)
d1 = w.s([w.s([efm], 'oveq2d', '( %s -> ( CC _D exp ) = ( CC _D %s ) )' % (A0, MP('y', 'CC', '( exp ` y )')))], 'eqcomd',
         '( %s -> ( CC _D %s ) = ( CC _D exp ) )' % (A0, MP('y', 'CC', '( exp ` y )')))
dcy = w.s([w.s([d1, dvefd], 'eqtrd', '( %s -> ( CC _D %s ) = exp )' % (A0, MP('y', 'CC', '( exp ` y )'))), efm], 'eqtrd',
          '( %s -> ( CC _D %s ) = %s )' % (A0, MP('y', 'CC', '( exp ` y )'), MP('y', 'CC', '( exp ` y )')))
sty = w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = ( exp ` %s ) )' % (ARG, ARG))
w.qed([ce, ce, argc, et2z, eyc, eyc, dcm, dcy, sty, sty], 'dvmptco',
      '( %s -> ( CC _D %s ) = %s )' % (A0, G('CC'), MP('z', 'CC', '( ( exp ` %s ) x. ( E x. ( 2 x. z ) ) )' % ARG))); run1(w)

# ---- holgau ----------------------------------------------------------------
w = W('holgau', 'The Gaussian normaliser is holomorphic on any open set of complex numbers.')
A0 = '( D e. %s /\\ D C_ CC /\\ ( E e. CC /\\ Q e. CC ) )' % TOP
A1 = '( %s /\\ z e. CC )' % A0
A2 = '( %s /\\ z e. D )' % A0
RHS = '( ( exp ` %s ) x. ( E x. ( 2 x. z ) ) )' % ARG
dop = w.s([], 'simp1', '( %s -> D e. %s )' % (A0, TOP))
dcc = w.s([], 'simp2', '( %s -> D C_ CC )' % A0)
eq0 = w.s([], 'simp3', '( %s -> ( E e. CC /\\ Q e. CC ) )' % A0)
ec = w.s([eq0, w.inst('simpl')], 'syl', '( %s -> E e. CC )' % A0)
qc = w.s([eq0, w.inst('simpr')], 'syl', '( %s -> Q e. CC )' % A0)
cnc = w.s([ec, qc, dcc, w.inst('gaucn')], 'syl3anc', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, G('D')))
ce = cnel(w, A0)
zc = w.s([], 'simpr', '( %s -> z e. CC )' % A1)
ec1 = w.s([ec], 'adantr', '( %s -> E e. CC )' % A1)
qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
argc = w.s([ec1, w.s([w.s([zc], 'sqcld', '( %s -> ( z ^ 2 ) e. CC )' % A1), qc1], 'subcld', '( %s -> ( ( z ^ 2 ) - Q ) e. CC )' % A1)],
           'mulcld', '( %s -> %s e. CC )' % (A1, ARG))
eac = w.s([argc, w.inst('efcl')], 'syl', '( %s -> ( exp ` %s ) e. CC )' % (A1, ARG))
rhsc = w.s([eac, w.s([ec1, w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A1), zc], 'mulcld', '( %s -> ( 2 x. z ) e. CC )' % A1)],
                     'mulcld', '( %s -> ( E x. ( 2 x. z ) ) e. CC )' % A1)], 'mulcld', '( %s -> %s e. CC )' % (A1, RHS))
dvcc = w.s([ec, qc, w.inst('dvgau')], 'syl2anc', '( %s -> ( CC _D %s ) = %s )' % (A0, G('CC'), MP('z', 'CC', RHS)))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
dvd = w.s([ce, eac, rhsc, dvcc, dcc, jr, ej, dop], 'dvmptres', '( %s -> ( CC _D %s ) = %s )' % (A0, G('D'), MP('z', 'D', RHS)))
zd = w.s([], 'simpr', '( %s -> z e. D )' % A2)
zc2 = w.s([w.s([dcc], 'adantr', '( %s -> D C_ CC )' % A2), zd], 'sseldd', '( %s -> z e. CC )' % A2)
ec2 = w.s([ec], 'adantr', '( %s -> E e. CC )' % A2)
qc2 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A2)
argc2 = w.s([ec2, w.s([w.s([zc2], 'sqcld', '( %s -> ( z ^ 2 ) e. CC )' % A2), qc2], 'subcld', '( %s -> ( ( z ^ 2 ) - Q ) e. CC )' % A2)],
            'mulcld', '( %s -> %s e. CC )' % (A2, ARG))
eac2 = w.s([argc2, w.inst('efcl')], 'syl', '( %s -> ( exp ` %s ) e. CC )' % (A2, ARG))
rhsc2 = w.s([eac2, w.s([ec2, w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A2), zc2], 'mulcld', '( %s -> ( 2 x. z ) e. CC )' % A2)],
                       'mulcld', '( %s -> ( E x. ( 2 x. z ) ) e. CC )' % A2)], 'mulcld', '( %s -> %s e. CC )' % (A2, RHS))
ds = dvdom(w, A0, G('D'), 'z', 'D', RHS, dvd, rhsc2)
w.qed([cnc, ds], 'jca', '( %s -> %s )' % (A0, HOLG(G('D')))); run1(w)

# ---- absgau ----------------------------------------------------------------
w = W('absgau', 'The modulus of the Gaussian normaliser at a point, in terms of the real and imaginary parts.')
A0 = '( Z e. CC /\\ E e. RR /\\ Q e. RR )'
RZ = '( Re ` Z )'; IZ = '( Im ` Z )'
AR = '( E x. ( ( Z ^ 2 ) - Q ) )'
TGT = '( exp ` ( E x. ( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - Q ) ) )' % (RZ, IZ)
zc = w.s([], 'simp1', '( %s -> Z e. CC )' % A0)
er = w.s([], 'simp2', '( %s -> E e. RR )' % A0)
qr = w.s([], 'simp3', '( %s -> Q e. RR )' % A0)
ec = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
qc = w.s([qr], 'recnd', '( %s -> Q e. CC )' % A0)
sqc = w.s([zc], 'sqcld', '( %s -> ( Z ^ 2 ) e. CC )' % A0)
argc = w.s([ec, w.s([sqc, qc], 'subcld', '( %s -> ( ( Z ^ 2 ) - Q ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, AR))
ae = w.s([argc, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` %s ) ) = ( exp ` ( Re ` %s ) ) )' % (A0, AR, AR))
r1 = w.s([er, w.s([sqc, qc], 'subcld', '( %s -> ( ( Z ^ 2 ) - Q ) e. CC )' % A0), w.inst('remul2')], 'syl2anc',
         '( %s -> ( Re ` %s ) = ( E x. ( Re ` ( ( Z ^ 2 ) - Q ) ) ) )' % (A0, AR))
r2 = w.s([sqc, qc, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( ( Z ^ 2 ) - Q ) ) = ( ( Re ` ( Z ^ 2 ) ) - ( Re ` Q ) ) )' % A0)
r3 = w.s([qr, w.inst('rere')], 'syl', '( %s -> ( Re ` Q ) = Q )' % A0)
sq1 = w.s([w.s([zc, w.inst('sqval')], 'syl', '( %s -> ( Z ^ 2 ) = ( Z x. Z ) )' % A0)], 'fveq2d',
          '( %s -> ( Re ` ( Z ^ 2 ) ) = ( Re ` ( Z x. Z ) ) )' % A0)
sq2 = w.s([zc, zc, w.inst('remul')], 'syl2anc', '( %s -> ( Re ` ( Z x. Z ) ) = ( ( %s x. %s ) - ( %s x. %s ) ) )' % (A0, RZ, RZ, IZ, IZ))
rzc = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
izc = w.s([zc], 'imcld', '( %s -> %s e. RR )' % (A0, IZ))
sq3 = w.s([w.s([w.s([rzc], 'recnd', '( %s -> %s e. CC )' % (A0, RZ))], 'sqvald', '( %s -> ( %s ^ 2 ) = ( %s x. %s ) )' % (A0, RZ, RZ, RZ))],
          'eqcomd', '( %s -> ( %s x. %s ) = ( %s ^ 2 ) )' % (A0, RZ, RZ, RZ))
sq4 = w.s([w.s([w.s([izc], 'recnd', '( %s -> %s e. CC )' % (A0, IZ))], 'sqvald', '( %s -> ( %s ^ 2 ) = ( %s x. %s ) )' % (A0, IZ, IZ, IZ))],
          'eqcomd', '( %s -> ( %s x. %s ) = ( %s ^ 2 ) )' % (A0, IZ, IZ, IZ))
sq5 = w.s([sq3, sq4], 'oveq12d', '( %s -> ( ( %s x. %s ) - ( %s x. %s ) ) = ( ( %s ^ 2 ) - ( %s ^ 2 ) ) )' % (A0, RZ, RZ, IZ, IZ, RZ, IZ))
rsq = w.s([w.s([sq1, sq2], 'eqtrd', '( %s -> ( Re ` ( Z ^ 2 ) ) = ( ( %s x. %s ) - ( %s x. %s ) ) )' % (A0, RZ, RZ, IZ, IZ)), sq5],
          'eqtrd', '( %s -> ( Re ` ( Z ^ 2 ) ) = ( ( %s ^ 2 ) - ( %s ^ 2 ) ) )' % (A0, RZ, IZ))
r4 = w.s([r2, w.s([rsq, r3], 'oveq12d', '( %s -> ( ( Re ` ( Z ^ 2 ) ) - ( Re ` Q ) ) = ( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - Q ) )' % (A0, RZ, IZ))],
         'eqtrd', '( %s -> ( Re ` ( ( Z ^ 2 ) - Q ) ) = ( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - Q ) )' % (A0, RZ, IZ))
rfin = w.s([r1, w.s([r4], 'oveq2d', '( %s -> ( E x. ( Re ` ( ( Z ^ 2 ) - Q ) ) ) = ( E x. ( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - Q ) ) )' % (A0, RZ, IZ))],
           'eqtrd', '( %s -> ( Re ` %s ) = ( E x. ( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - Q ) ) )' % (A0, AR, RZ, IZ))
w.qed([ae, w.s([rfin], 'fveq2d', '( %s -> ( exp ` ( Re ` %s ) ) = %s )' % (A0, AR, TGT))], 'eqtrd',
      '( %s -> ( abs ` ( exp ` %s ) ) = %s )' % (A0, AR, TGT)); run1(w)

# ---- dvgaud ----------------------------------------------------------------
w = W('dvgaud', 'The derivative of the Gaussian normaliser restricted to an open set of complex numbers.')
A0 = '( D e. %s /\\ D C_ CC /\\ ( E e. CC /\\ Q e. CC ) )' % TOP
A1 = '( %s /\\ z e. CC )' % A0
RHS = '( ( exp ` %s ) x. ( E x. ( 2 x. z ) ) )' % ARG
dop = w.s([], 'simp1', '( %s -> D e. %s )' % (A0, TOP))
dcc = w.s([], 'simp2', '( %s -> D C_ CC )' % A0)
eq0 = w.s([], 'simp3', '( %s -> ( E e. CC /\\ Q e. CC ) )' % A0)
ec = w.s([eq0, w.inst('simpl')], 'syl', '( %s -> E e. CC )' % A0)
qc = w.s([eq0, w.inst('simpr')], 'syl', '( %s -> Q e. CC )' % A0)
ce = cnel(w, A0)
zc = w.s([], 'simpr', '( %s -> z e. CC )' % A1)
ec1 = w.s([ec], 'adantr', '( %s -> E e. CC )' % A1)
qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
argc = w.s([ec1, w.s([w.s([zc], 'sqcld', '( %s -> ( z ^ 2 ) e. CC )' % A1), qc1], 'subcld', '( %s -> ( ( z ^ 2 ) - Q ) e. CC )' % A1)],
           'mulcld', '( %s -> %s e. CC )' % (A1, ARG))
eac = w.s([argc, w.inst('efcl')], 'syl', '( %s -> ( exp ` %s ) e. CC )' % (A1, ARG))
rhsc = w.s([eac, w.s([ec1, w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A1), zc], 'mulcld', '( %s -> ( 2 x. z ) e. CC )' % A1)],
                     'mulcld', '( %s -> ( E x. ( 2 x. z ) ) e. CC )' % A1)], 'mulcld', '( %s -> %s e. CC )' % (A1, RHS))
dvcc = w.s([ec, qc, w.inst('dvgau')], 'syl2anc', '( %s -> ( CC _D %s ) = %s )' % (A0, G('CC'), MP('z', 'CC', RHS)))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
w.qed([ce, eac, rhsc, dvcc, dcc, jr, ej, dop], 'dvmptres', '( %s -> ( CC _D %s ) = %s )' % (A0, G('D'), MP('z', 'D', RHS))); run1(w)
