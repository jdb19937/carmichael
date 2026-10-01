"""C4, Gamma block 6: the vertical strip bound with an explicit rate."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import num

RZ = '( Re ` Z )'
V = '( abs ` ( Im ` Z ) )'
T = '( 2 ^c -u ( %s / 2 ) )' % V
ZP = '( Z e. CC /\\ 0 < %s )' % RZ
HQ = 'A. j e. ( 1 ... M ) ( 2 x. ( %s + j ) ) <_ %s' % (RZ, V)
PHM = '( %s /\\ ( M e. NN0 /\\ %s ) )' % (ZP, HQ)


def rlit(w, A, t, k):
    return w.s([num.fact(w, t, k)], 'a1i', '( %s -> %s )' %
               (A, {'RR': '%s e. RR', 'RR+': '%s e. RR+', 'CC': '%s e. CC',
                    'NN0': '%s e. NN0', 'ZZ': '%s e. ZZ', 'ne0': '%s =/= 0',
                    'ge0': '0 <_ %s', 'gt0': '0 < %s'}[k] % t))


def vctx(w, A, zc):
    """steps for ( abs ` ( Im ` Z ) ) and ( 2 ^c -u ( V / 2 ) )"""
    vr = w.s([w.s([w.s([zc], 'imcld', '( %s -> ( Im ` Z ) e. RR )' % A)], 'recnd',
                  '( %s -> ( Im ` Z ) e. CC )' % A)], 'abscld', '( %s -> %s e. RR )' % (A, V))
    vh = w.s([vr, rlit(w, A, '2', 'RR'), rlit(w, A, '2', 'ne0')], 'redivcld',
             '( %s -> ( %s / 2 ) e. RR )' % (A, V))
    trp = w.s([rlit(w, A, '2', 'RR+'), w.s([vh], 'renegcld', '( %s -> -u ( %s / 2 ) e. RR )' % (A, V))],
              'rpcxpcld', '( %s -> %s e. RR+ )' % (A, T))
    return vr, vh, trp


# ---------------------------------------------------------------- gamvbc
PHC = '( %s /\\ ( M e. NN0 /\\ %s ) /\\ ( 1 / ( 2 ^ M ) ) <_ ( ; 1 6 x. %s ) )' % (ZP, HQ, T)
w = W('gamvbc', 'The vertical decay of the gamma function, given a numeric bound on '
      'the factor ` ( 1 / ( 2 ^ M ) ) ` that ~ gamvb0 produces.')
zp = w.s([], 'simp1', '( %s -> %s )' % (PHC, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PHC)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PHC, RZ))
mh = w.s([], 'simp2', '( %s -> ( M e. NN0 /\\ %s ) )' % (PHC, HQ))
mz = w.s([w.s([mh, w.inst('simpl')], 'syl', '( %s -> M e. NN0 )' % PHC), w.inst('nn0z')], 'syl',
         '( %s -> M e. ZZ )' % PHC)
bnd = w.s([], 'simp3', '( %s -> ( 1 / ( 2 ^ M ) ) <_ ( ; 1 6 x. %s ) )' % (PHC, T))
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (PHC, RZ))
grp = w.s([w.s([rzr, z0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (PHC, RZ, RZ)), w.inst('gamrrp')],
          'syl', '( %s -> ( _G ` %s ) e. RR+ )' % (PHC, RZ))
gr = w.s([grp], 'rpred', '( %s -> ( _G ` %s ) e. RR )' % (PHC, RZ))
gc = w.s([grp], 'rpcnd', '( %s -> ( _G ` %s ) e. CC )' % (PHC, RZ))
g0 = w.s([grp], 'rpge0d', '( %s -> 0 <_ ( _G ` %s ) )' % (PHC, RZ))
vr, vh, trp = vctx(w, PHC, zc)
vb0 = w.s([w.s([zp, mh], 'jca', '( %s -> %s )' % (PHC, PHM)), w.inst('gamvb0')], 'syl',
          '( %s -> ( abs ` ( _G ` Z ) ) <_ ( ( _G ` %s ) / ( 2 ^ M ) ) )' % (PHC, RZ))
pw = w.s([rlit(w, PHC, '2', 'RR+'), mz], 'rpexpcld', '( %s -> ( 2 ^ M ) e. RR+ )' % PHC)
rec = w.s([rlit(w, PHC, '1', 'RR+'), pw], 'rpdivcld', '( %s -> ( 1 / ( 2 ^ M ) ) e. RR+ )' % PHC)
dr = w.s([gc, w.s([pw], 'rpcnd', '( %s -> ( 2 ^ M ) e. CC )' % PHC),
          w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHC)], 'divrecd',
         '( %s -> ( ( _G ` %s ) / ( 2 ^ M ) ) = ( ( _G ` %s ) x. ( 1 / ( 2 ^ M ) ) ) )' % (PHC, RZ, RZ))
r16 = rlit(w, PHC, '; 1 6', 'RR')
c16 = rlit(w, PHC, '; 1 6', 'CC')
prod = w.s([r16, w.s([trp], 'rpred', '( %s -> %s e. RR )' % (PHC, T))], 'remulcld',
           '( %s -> ( ; 1 6 x. %s ) e. RR )' % (PHC, T))
step = w.s([w.s([rec], 'rpred', '( %s -> ( 1 / ( 2 ^ M ) ) e. RR )' % PHC), prod, gr, g0, bnd], 'lemul2ad',
           '( %s -> ( ( _G ` %s ) x. ( 1 / ( 2 ^ M ) ) ) <_ ( ( _G ` %s ) x. ( ; 1 6 x. %s ) ) )' % (PHC, RZ, RZ, T))
assoc = w.s([gc, c16, w.s([trp], 'rpcnd', '( %s -> %s e. CC )' % (PHC, T))], 'mul12d',
            '( %s -> ( ( _G ` %s ) x. ( ; 1 6 x. %s ) ) = ( ; 1 6 x. ( ( _G ` %s ) x. %s ) ) )' % (PHC, RZ, T, RZ, T))
assoc2 = w.s([c16, gc, w.s([trp], 'rpcnd', '( %s -> %s e. CC )' % (PHC, T))], 'mulassd',
             '( %s -> ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) = ( ; 1 6 x. ( ( _G ` %s ) x. %s ) ) )' % (PHC, RZ, T, RZ, T))
eqf = w.s([assoc, w.s([assoc2], 'eqcomd',
                      '( %s -> ( ; 1 6 x. ( ( _G ` %s ) x. %s ) ) = ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (PHC, RZ, T, RZ, T))],
          'eqtrd', '( %s -> ( ( _G ` %s ) x. ( ; 1 6 x. %s ) ) = ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (PHC, RZ, T, RZ, T))
mid = w.s([step, eqf], 'breqtrd',
          '( %s -> ( ( _G ` %s ) x. ( 1 / ( 2 ^ M ) ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (PHC, RZ, RZ, T))
gzc = w.s([w.s([w.s([zc, z0], 'jca', '( %s -> %s )' % (PHC, ZP)), w.inst('zrenn')], 'syl',
               '( %s -> Z e. ( CC \\ ( ZZ \\ NN ) ) )' % PHC), w.inst('gamcl')], 'syl',
          '( %s -> ( _G ` Z ) e. CC )' % PHC)
agr = w.s([gzc], 'abscld', '( %s -> ( abs ` ( _G ` Z ) ) e. RR )' % PHC)
qr = w.s([gr, w.s([pw], 'rpred', '( %s -> ( 2 ^ M ) e. RR )' % PHC),
          w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHC)], 'redivcld',
         '( %s -> ( ( _G ` %s ) / ( 2 ^ M ) ) e. RR )' % (PHC, RZ))
fr = w.s([w.s([r16, gr], 'remulcld', '( %s -> ( ; 1 6 x. ( _G ` %s ) ) e. RR )' % (PHC, RZ)),
          w.s([trp], 'rpred', '( %s -> %s e. RR )' % (PHC, T))], 'remulcld',
         '( %s -> ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) e. RR )' % (PHC, RZ, T))
w.qed([agr, qr, fr, vb0, w.s([dr, mid], 'eqbrtrd',
                             '( %s -> ( ( _G ` %s ) / ( 2 ^ M ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (PHC, RZ, RZ, T))],
      'letrd', '( %s -> ( abs ` ( _G ` Z ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (PHC, RZ, T))
run4(w)

# ---------------------------------------------------------------- gamvbl
AL = '( %s /\\ %s <_ 8 )' % (ZP, V)
w = W('gamvbl', 'The vertical bound of ~ gamvbc below height eight, where the '
      'constant alone suffices.')
zp = w.s([], 'simpl', '( %s -> %s )' % (AL, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % AL)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (AL, RZ))
hy = w.s([], 'simpr', '( %s -> %s <_ 8 )' % (AL, V))
vr, vh, trp = vctx(w, AL, zc)
# the vacuous quantifier at M = 0
fz0 = w.s([], 'fz10', '( 1 ... 0 ) = (/)')
r0 = w.s([], 'ral0', 'A. j e. (/) ( 2 x. ( %s + j ) ) <_ %s' % (RZ, V))
rq = w.s([r0, w.s([w.s([fz0], 'eqcomi', '(/) = ( 1 ... 0 )'), w.inst('raleq')], 'ax-mp',
                  '( A. j e. (/) ( 2 x. ( %s + j ) ) <_ %s <-> A. j e. ( 1 ... 0 ) ( 2 x. ( %s + j ) ) <_ %s )' % (RZ, V, RZ, V))],
         'mpbi', 'A. j e. ( 1 ... 0 ) ( 2 x. ( %s + j ) ) <_ %s' % (RZ, V))
rqd = w.s([rq], 'a1i', '( %s -> A. j e. ( 1 ... 0 ) ( 2 x. ( %s + j ) ) <_ %s )' % (AL, RZ, V))
# ( 1 / ( 2 ^ 0 ) ) = 1
e0 = w.s([w.s([num.fact(w, '2', 'CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')], 'a1i',
         '( %s -> ( 2 ^ 0 ) = 1 )' % AL)
d1 = w.s([e0, w.s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( %s -> ( 1 / 1 ) = 1 )' % AL)],
         'jca', 'dummy')
w.lines.pop()
q1 = w.s([w.s([e0], 'oveq2d', '( %s -> ( 1 / ( 2 ^ 0 ) ) = ( 1 / 1 ) )' % AL),
          w.s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( %s -> ( 1 / 1 ) = 1 )' % AL)],
         'eqtrd', '( %s -> ( 1 / ( 2 ^ 0 ) ) = 1 )' % AL)
# ( 2 ^c -u 4 ) = ( 1 / ; 1 6 )
cx4 = w.s([num.fact(w, '2', 'CC'), num.fact(w, '2', 'ne0'), num.fact(w, '4', 'CC'), w.inst('cxpneg')],
          'mp3an', '( 2 ^c -u 4 ) = ( 1 / ( 2 ^c 4 ) )')
ce4 = w.s([num.fact(w, '2', 'CC'), num.fact(w, '4', 'NN0'), w.inst('cxpexp')], 'mp2an', '( 2 ^c 4 ) = ( 2 ^ 4 )')
e16 = w.s([ce4, w.s([], '2exp4', '( 2 ^ 4 ) = ; 1 6')], 'eqtri', '( 2 ^c 4 ) = ; 1 6')
cx4b = w.s([cx4, w.s([e16], 'oveq2i', '( 1 / ( 2 ^c 4 ) ) = ( 1 / ; 1 6 )')], 'eqtri', '( 2 ^c -u 4 ) = ( 1 / ; 1 6 )')
# -u 4 <_ -u ( V / 2 )
bi = w.s([vr, rlit(w, AL, '4', 'RR'), w.s([rlit(w, AL, '2', 'RR'), rlit(w, AL, '2', 'gt0')], 'jca',
                                          '( %s -> ( 2 e. RR /\\ 0 < 2 ) )' % AL), w.inst('ledivmul')],
         'syl3anc', '( %s -> ( ( %s / 2 ) <_ 4 <-> %s <_ ( 2 x. 4 ) ) )' % (AL, V, V))
t24 = w.s([num.mul_nat(w, 2, 4)], 'a1i', '( %s -> ( 2 x. 4 ) = 8 )' % AL)
vle4 = w.s([w.s([hy, w.s([t24], 'eqcomd', '( %s -> 8 = ( 2 x. 4 ) )' % AL)], 'breqtrd',
                '( %s -> %s <_ ( 2 x. 4 ) )' % (AL, V)), bi], 'mpbird', '( %s -> ( %s / 2 ) <_ 4 )' % (AL, V))
nle = w.s([vle4, w.s([vh, rlit(w, AL, '4', 'RR')], 'lenegd',
                     '( %s -> ( ( %s / 2 ) <_ 4 <-> -u 4 <_ -u ( %s / 2 ) ) )' % (AL, V, V))],
          'mpbid', '( %s -> -u 4 <_ -u ( %s / 2 ) )' % (AL, V))
cle = w.s([rlit(w, AL, '2', 'RR'), num.fact(w, '2', 'ge1'), w.s([rlit(w, AL, '4', 'RR')], 'renegcld',
                                                               '( %s -> -u 4 e. RR )' % AL),
           w.s([vh], 'renegcld', '( %s -> -u ( %s / 2 ) e. RR )' % (AL, V)), nle], 'jca', 'dummy')
w.lines.pop()
one2 = w.s([num.fact(w, '2', 'ge1')], 'a1i', '( %s -> 1 <_ 2 )' % AL)
cle = w.s([w.s([rlit(w, AL, '2', 'RR'), one2], 'jca', '( %s -> ( 2 e. RR /\\ 1 <_ 2 ) )' % AL),
           w.s([w.s([rlit(w, AL, '4', 'RR')], 'renegcld', '( %s -> -u 4 e. RR )' % AL),
                w.s([vh], 'renegcld', '( %s -> -u ( %s / 2 ) e. RR )' % (AL, V))], 'jca',
               '( %s -> ( -u 4 e. RR /\\ -u ( %s / 2 ) e. RR ) )' % (AL, V)), nle, w.inst('cxplea')],
          'syl3anc', '( %s -> ( 2 ^c -u 4 ) <_ %s )' % (AL, T))
rle = w.s([w.s([cx4b], 'a1i', '( %s -> ( 2 ^c -u 4 ) = ( 1 / ; 1 6 ) )' % AL), cle], 'eqbrtrrd',
          '( %s -> ( 1 / ; 1 6 ) <_ %s )' % (AL, T))
r16 = rlit(w, AL, '; 1 6', 'RR')
mul = w.s([w.s([rlit(w, AL, '1', 'RR'), r16, rlit(w, AL, '; 1 6', 'ne0')], 'redivcld',
               '( %s -> ( 1 / ; 1 6 ) e. RR )' % AL),
           w.s([trp], 'rpred', '( %s -> %s e. RR )' % (AL, T)), r16,
           rlit(w, AL, '; 1 6', 'ge0'), rle], 'lemul2ad',
          '( %s -> ( ; 1 6 x. ( 1 / ; 1 6 ) ) <_ ( ; 1 6 x. %s ) )' % (AL, T))
rid = w.s([w.s([num.fact(w, '; 1 6', 'CC'), num.fact(w, '; 1 6', 'ne0'), w.inst('recid')], 'mp2an',
               '( ; 1 6 x. ( 1 / ; 1 6 ) ) = 1')], 'a1i', '( %s -> ( ; 1 6 x. ( 1 / ; 1 6 ) ) = 1 )' % AL)
num1 = w.s([q1, w.s([rid, mul], 'eqbrtrrd', '( %s -> 1 <_ ( ; 1 6 x. %s ) )' % (AL, T))], 'eqbrtrd',
           '( %s -> ( 1 / ( 2 ^ 0 ) ) <_ ( ; 1 6 x. %s ) )' % (AL, T))
w.qed([zp, w.s([w.s([num.fact(w, '0', 'NN0')], 'a1i', '( %s -> 0 e. NN0 )' % AL), rqd], 'jca',
               '( %s -> ( 0 e. NN0 /\\ A. j e. ( 1 ... 0 ) ( 2 x. ( %s + j ) ) <_ %s ) )' % (AL, RZ, V)), num1,
       w.inst('gamvbc')],
      'syl3anc', '( %s -> ( abs ` ( _G ` Z ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (AL, RZ, T))
run4(w)

# ---------------------------------------------------------------- gamvbh
AH = '( ( %s /\\ %s <_ 3 ) /\\ 8 <_ %s )' % (ZP, RZ, V)
FL = '( |_ ` ( %s / 2 ) )' % V
M0 = '( %s - 3 )' % FL
PW = '( 2 ^c ( %s / 2 ) )' % V
w = W('gamvbh', 'The vertical bound of ~ gamvbc above height eight, at the index '
      '` M = ( |_ ` ( ( abs ` ( Im ` Z ) ) / 2 ) ) - 3 `.')
zp = w.s([w.s([], 'simpl', '( %s -> ( %s /\\ %s <_ 3 ) )' % (AH, ZP, RZ)), w.inst('simpl')], 'syl',
         '( %s -> %s )' % (AH, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % AH)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (AH, RZ))
rz3 = w.s([w.s([], 'simpl', '( %s -> ( %s /\\ %s <_ 3 ) )' % (AH, ZP, RZ)), w.inst('simpr')], 'syl',
          '( %s -> %s <_ 3 )' % (AH, RZ))
hy = w.s([], 'simpr', '( %s -> 8 <_ %s )' % (AH, V))
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (AH, RZ))
vr, vh, trp = vctx(w, AH, zc)
vc = w.s([vh], 'recnd', '( %s -> ( %s / 2 ) e. CC )' % (AH, V))
flz = w.s([vh, w.inst('flcl')], 'syl', '( %s -> %s e. ZZ )' % (AH, FL))
flr = w.s([flz], 'zred', '( %s -> %s e. RR )' % (AH, FL))
flc = w.s([flr], 'recnd', '( %s -> %s e. CC )' % (AH, FL))
# 4 <_ ( V / 2 )
t42 = w.s([num.mul_nat(w, 4, 2)], 'a1i', '( %s -> ( 4 x. 2 ) = 8 )' % AH)
bi2 = w.s([rlit(w, AH, '4', 'RR'), vr, w.s([rlit(w, AH, '2', 'RR'), rlit(w, AH, '2', 'gt0')], 'jca',
                                           '( %s -> ( 2 e. RR /\\ 0 < 2 ) )' % AH), w.inst('lemuldiv')],
          'syl3anc', '( %s -> ( ( 4 x. 2 ) <_ %s <-> 4 <_ ( %s / 2 ) ) )' % (AH, V, V))
v4 = w.s([w.s([t42, hy], 'eqbrtrd', '( %s -> ( 4 x. 2 ) <_ %s )' % (AH, V)), bi2], 'mpbid',
         '( %s -> 4 <_ ( %s / 2 ) )' % (AH, V))
fl4 = w.s([v4, w.s([vh, rlit(w, AH, '4', 'ZZ'), w.inst('flge')], 'syl2anc',
                   '( %s -> ( 4 <_ ( %s / 2 ) <-> 4 <_ %s ) )' % (AH, V, FL))], 'mpbid',
          '( %s -> 4 <_ %s )' % (AH, FL))
mz = w.s([flz, rlit(w, AH, '3', 'ZZ')], 'zsubcld', '( %s -> %s e. ZZ )' % (AH, M0))
l34 = w.s([w.s([w.s([], '3lt4', '3 < 4'), w.s([w.s([], '3re', '3 e. RR'), w.s([], '4re', '4 e. RR'), w.inst('ltle')], 'mp2an',
                                              '( 3 < 4 -> 3 <_ 4 )')], 'ax-mp', '3 <_ 4')], 'a1i', '( %s -> 3 <_ 4 )' % AH)
fl3 = w.s([rlit(w, AH, '3', 'RR'), rlit(w, AH, '4', 'RR'), flr, l34, fl4], 'letrd', '( %s -> 3 <_ %s )' % (AH, FL))
mge0 = w.s([fl3, w.s([flr, rlit(w, AH, '3', 'RR')], 'subge0d', '( %s -> ( 0 <_ %s <-> 3 <_ %s ) )' % (AH, M0, FL))],
           'mpbird', '( %s -> 0 <_ %s )' % (AH, M0))
mn0 = w.s([mz, mge0], 'jca', '( %s -> ( %s e. ZZ /\\ 0 <_ %s ) )' % (AH, M0, M0))
mn0 = w.s([mn0, w.s([w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (M0, M0, M0))], 'a1i',
                    '( %s -> ( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) ) )' % (AH, M0, M0, M0))], 'mpbird',
           '( %s -> %s e. NN0 )' % (AH, M0))
# ( 3 + M0 ) = FL
pn3 = w.s([rlit(w, AH, '3', 'CC'), flc], 'pncan3d', '( %s -> ( 3 + %s ) = %s )' % (AH, M0, FL))
# the quantified hypothesis
PJ = '( %s /\\ j e. ( 1 ... %s ) )' % (AH, M0)
jfz = w.s([], 'simpr', '( %s -> j e. ( 1 ... %s ) )' % (PJ, M0))
jr = w.s([w.s([jfz, w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % PJ)], 'nnred', '( %s -> j e. RR )' % PJ)
jle = w.s([jfz, w.inst('elfzle2')], 'syl', '( %s -> j <_ %s )' % (PJ, M0))
mr = w.s([flr, rlit(w, AH, '3', 'RR')], 'resubcld', '( %s -> %s e. RR )' % (AH, M0))
add = w.s([w.s([rzr], 'adantr', '( %s -> %s e. RR )' % (PJ, RZ)), rlit(w, PJ, '3', 'RR'), jr,
           w.s([mr], 'adantr', '( %s -> %s e. RR )' % (PJ, M0)),
           w.s([rz3], 'adantr', '( %s -> %s <_ 3 )' % (PJ, RZ)), jle], 'le2addd',
          '( %s -> ( %s + j ) <_ ( 3 + %s ) )' % (PJ, RZ, M0))
addfl = w.s([add, w.s([pn3], 'adantr', '( %s -> ( 3 + %s ) = %s )' % (PJ, M0, FL))], 'breqtrd',
            '( %s -> ( %s + j ) <_ %s )' % (PJ, RZ, FL))
flle = w.s([w.s([vh], 'adantr', '( %s -> ( %s / 2 ) e. RR )' % (PJ, V)), w.inst('flle')], 'syl',
           '( %s -> %s <_ ( %s / 2 ) )' % (PJ, FL, V))
chain = w.s([w.s([w.s([rzr], 'adantr', '( %s -> %s e. RR )' % (PJ, RZ)), jr], 'readdcld',
                 '( %s -> ( %s + j ) e. RR )' % (PJ, RZ)),
             w.s([flr], 'adantr', '( %s -> %s e. RR )' % (PJ, FL)),
             w.s([vh], 'adantr', '( %s -> ( %s / 2 ) e. RR )' % (PJ, V)), addfl, flle], 'letrd',
            '( %s -> ( %s + j ) <_ ( %s / 2 ) )' % (PJ, RZ, V))
mul2 = w.s([w.s([w.s([rzr], 'adantr', '( %s -> %s e. RR )' % (PJ, RZ)), jr], 'readdcld',
                '( %s -> ( %s + j ) e. RR )' % (PJ, RZ)),
            w.s([vh], 'adantr', '( %s -> ( %s / 2 ) e. RR )' % (PJ, V)), rlit(w, PJ, '2', 'RR'),
            rlit(w, PJ, '2', 'ge0'), chain], 'lemul2ad',
           '( %s -> ( 2 x. ( %s + j ) ) <_ ( 2 x. ( %s / 2 ) ) )' % (PJ, RZ, V))
dc2 = w.s([w.s([w.s([vr], 'adantr', '( %s -> %s e. RR )' % (PJ, V))], 'recnd', '( %s -> %s e. CC )' % (PJ, V)),
           rlit(w, PJ, '2', 'CC'), rlit(w, PJ, '2', 'ne0')], 'divcan2d',
          '( %s -> ( 2 x. ( %s / 2 ) ) = %s )' % (PJ, V, V))
each = w.s([mul2, dc2], 'breqtrd', '( %s -> ( 2 x. ( %s + j ) ) <_ %s )' % (PJ, RZ, V))
quant = w.s([each], 'ralrimiva', '( %s -> A. j e. ( 1 ... %s ) ( 2 x. ( %s + j ) ) <_ %s )' % (AH, M0, RZ, V))

# ---- the numeric factor: ( 1 / ( 2 ^ M0 ) ) <_ ( ; 1 6 x. T )
# ( V / 2 ) - 4 <_ M0
flt = w.s([vh, w.inst('flltp1')], 'syl', '( %s -> ( %s / 2 ) < ( %s + 1 ) )' % (AH, V, FL))
sub4 = w.s([vh, w.s([flr, rlit(w, AH, '1', 'RR')], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (AH, FL)),
            rlit(w, AH, '4', 'RR'), flt], 'ltsub1dd',
           '( %s -> ( ( %s / 2 ) - 4 ) < ( ( %s + 1 ) - 4 ) )' % (AH, V, FL))
s41 = w.s([num.sub_nat(w, 4, 1)], 'a1i', '( %s -> ( 4 - 1 ) = 3 )' % AH)
ss3 = w.s([flc, rlit(w, AH, '4', 'CC'), rlit(w, AH, '1', 'CC')], 'subsub3d',
          '( %s -> ( %s - ( 4 - 1 ) ) = ( ( %s + 1 ) - 4 ) )' % (AH, FL, FL))
aa3 = w.s([w.s([w.s([s41], 'oveq2d', '( %s -> ( %s - ( 4 - 1 ) ) = %s )' % (AH, FL, M0))], 'eqcomd',
               '( %s -> %s = ( %s - ( 4 - 1 ) ) )' % (AH, M0, FL)), ss3], 'eqtrd',
          '( %s -> %s = ( ( %s + 1 ) - 4 ) )' % (AH, M0, FL))
mr2 = w.s([flr, rlit(w, AH, '3', 'RR')], 'resubcld', '( %s -> %s e. RR )' % (AH, M0))
vm4 = w.s([vh, rlit(w, AH, '4', 'RR')], 'resubcld', '( %s -> ( ( %s / 2 ) - 4 ) e. RR )' % (AH, V))
lem = w.s([vm4, mr2, w.s([sub4, w.s([aa3], 'eqcomd', '( %s -> ( ( %s + 1 ) - 4 ) = %s )' % (AH, FL, M0))], 'breqtrd', '( %s -> ( ( %s / 2 ) - 4 ) < %s )' % (AH, V, M0))],
          'ltled', '( %s -> ( ( %s / 2 ) - 4 ) <_ %s )' % (AH, V, M0))
# ( 2 ^c ( ( V / 2 ) - 4 ) ) <_ ( 2 ^c M0 )
one2 = w.s([num.fact(w, '2', 'ge1')], 'a1i', '( %s -> 1 <_ 2 )' % AH)
cle2 = w.s([w.s([rlit(w, AH, '2', 'RR'), one2], 'jca', '( %s -> ( 2 e. RR /\\ 1 <_ 2 ) )' % AH),
            w.s([vm4, mr2], 'jca', '( %s -> ( ( ( %s / 2 ) - 4 ) e. RR /\\ %s e. RR ) )' % (AH, V, M0)),
            lem, w.inst('cxplea')], 'syl3anc',
           '( %s -> ( 2 ^c ( ( %s / 2 ) - 4 ) ) <_ ( 2 ^c %s ) )' % (AH, V, M0))
cxe = w.s([rlit(w, AH, '2', 'CC'), rlit(w, AH, '2', 'ne0'), mz, w.inst('cxpexpz')], 'syl3anc',
          '( %s -> ( 2 ^c %s ) = ( 2 ^ %s ) )' % (AH, M0, M0))
cxs = w.s([w.s([rlit(w, AH, '2', 'CC'), rlit(w, AH, '2', 'ne0')], 'jca', '( %s -> ( 2 e. CC /\\ 2 =/= 0 ) )' % AH),
           vc, rlit(w, AH, '4', 'CC'), w.inst('cxpsub')], 'syl3anc',
          '( %s -> ( 2 ^c ( ( %s / 2 ) - 4 ) ) = ( %s / ( 2 ^c 4 ) ) )' % (AH, V, PW))
ce4 = w.s([num.fact(w, '2', 'CC'), num.fact(w, '4', 'NN0'), w.inst('cxpexp')], 'mp2an', '( 2 ^c 4 ) = ( 2 ^ 4 )')
e16 = w.s([w.s([ce4, w.s([], '2exp4', '( 2 ^ 4 ) = ; 1 6')], 'eqtri', '( 2 ^c 4 ) = ; 1 6')], 'a1i',
          '( %s -> ( 2 ^c 4 ) = ; 1 6 )' % AH)
cxs2 = w.s([cxs, w.s([e16], 'oveq2d', '( %s -> ( %s / ( 2 ^c 4 ) ) = ( %s / ; 1 6 ) )' % (AH, PW, PW))],
           'eqtrd', '( %s -> ( 2 ^c ( ( %s / 2 ) - 4 ) ) = ( %s / ; 1 6 ) )' % (AH, V, PW))
pwrp = w.s([rlit(w, AH, '2', 'RR+'), vh], 'rpcxpcld', '( %s -> %s e. RR+ )' % (AH, PW))
qrp = w.s([pwrp, rlit(w, AH, '; 1 6', 'RR+')], 'rpdivcld', '( %s -> ( %s / ; 1 6 ) e. RR+ )' % (AH, PW))
pw2 = w.s([rlit(w, AH, '2', 'RR+'), mz], 'rpexpcld', '( %s -> ( 2 ^ %s ) e. RR+ )' % (AH, M0))
key = w.s([w.s([cxs2], 'eqcomd', '( %s -> ( %s / ; 1 6 ) = ( 2 ^c ( ( %s / 2 ) - 4 ) ) )' % (AH, PW, V)),
           w.s([cle2, cxe], 'breqtrd', '( %s -> ( 2 ^c ( ( %s / 2 ) - 4 ) ) <_ ( 2 ^ %s ) )' % (AH, V, M0))],
          'eqbrtrd', '( %s -> ( %s / ; 1 6 ) <_ ( 2 ^ %s ) )' % (AH, PW, M0))
inv = w.s([qrp, pw2, rlit(w, AH, '1', 'RR'), rlit(w, AH, '1', 'ge0'), key], 'lediv2ad',
          '( %s -> ( 1 / ( 2 ^ %s ) ) <_ ( 1 / ( %s / ; 1 6 ) ) )' % (AH, M0, PW))
rd = w.s([w.s([w.s([pwrp], 'rpcnd', '( %s -> %s e. CC )' % (AH, PW)), w.s([pwrp], 'rpne0d', '( %s -> %s =/= 0 )' % (AH, PW))],
              'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (AH, PW, PW)),
          w.s([rlit(w, AH, '; 1 6', 'CC'), rlit(w, AH, '; 1 6', 'ne0')], 'jca',
              '( %s -> ( ; 1 6 e. CC /\\ ; 1 6 =/= 0 ) )' % AH), w.inst('recdiv')], 'syl2anc',
         '( %s -> ( 1 / ( %s / ; 1 6 ) ) = ( ; 1 6 / %s ) )' % (AH, PW, PW))
dr2 = w.s([rlit(w, AH, '; 1 6', 'CC'), w.s([pwrp], 'rpcnd', '( %s -> %s e. CC )' % (AH, PW)),
           w.s([pwrp], 'rpne0d', '( %s -> %s =/= 0 )' % (AH, PW))], 'divrecd',
          '( %s -> ( ; 1 6 / %s ) = ( ; 1 6 x. ( 1 / %s ) ) )' % (AH, PW, PW))
cn = w.s([rlit(w, AH, '2', 'CC'), rlit(w, AH, '2', 'ne0'), vc, w.inst('cxpneg')], 'syl3anc',
         '( %s -> %s = ( 1 / %s ) )' % (AH, T, PW))
fin = w.s([w.s([rd, dr2], 'eqtrd', '( %s -> ( 1 / ( %s / ; 1 6 ) ) = ( ; 1 6 x. ( 1 / %s ) ) )' % (AH, PW, PW)),
           w.s([w.s([cn], 'eqcomd', '( %s -> ( 1 / %s ) = %s )' % (AH, PW, T))], 'oveq2d',
               '( %s -> ( ; 1 6 x. ( 1 / %s ) ) = ( ; 1 6 x. %s ) )' % (AH, PW, T))],
          'eqtrd', '( %s -> ( 1 / ( %s / ; 1 6 ) ) = ( ; 1 6 x. %s ) )' % (AH, PW, T))
num1 = w.s([inv, fin], 'breqtrd', '( %s -> ( 1 / ( 2 ^ %s ) ) <_ ( ; 1 6 x. %s ) )' % (AH, M0, T))
w.qed([zp, w.s([mn0, quant], 'jca',
               '( %s -> ( %s e. NN0 /\\ A. j e. ( 1 ... %s ) ( 2 x. ( %s + j ) ) <_ %s ) )' % (AH, M0, M0, RZ, V)),
       num1, w.inst('gamvbc')],
      'syl3anc', '( %s -> ( abs ` ( _G ` Z ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (AH, RZ, T))
run4(w)

# ---------------------------------------------------------------- gamvb
AG = '( Z e. CC /\\ 0 < %s /\\ %s <_ 3 )' % (RZ, RZ)
w = W('gamvb', 'The gamma function decays at least like ` 2 ^ -u ( ( abs ` ( Im ` Z '
      ') ) / 2 ) ` on the vertical strip ` 0 < ( Re ` Z ) <_ 3 `, with the constant '
      '` ; 1 6 ` times its value on the real axis.  The two halves are ~ gamvbl '
      'and ~ gamvbh .')
GOAL = '( abs ` ( _G ` Z ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s )' % (RZ, T)
for tag, ante in (('l', '( %s /\\ %s <_ 8 )' % (AG, V)), ('h', '( %s /\\ -. %s <_ 8 )' % (AG, V))):
    zc = w.s([w.s([], 'simpl', '( %s -> %s )' % (ante, AG)), w.inst('simp1')], 'syl', '( %s -> Z e. CC )' % ante)
    z0 = w.s([w.s([], 'simpl', '( %s -> %s )' % (ante, AG)), w.inst('simp2')], 'syl', '( %s -> 0 < %s )' % (ante, RZ))
    r3 = w.s([w.s([], 'simpl', '( %s -> %s )' % (ante, AG)), w.inst('simp3')], 'syl', '( %s -> %s <_ 3 )' % (ante, RZ))
    zp2 = w.s([zc, z0], 'jca', '( %s -> %s )' % (ante, ZP))
    if tag == 'l':
        low = w.s([zp2, w.s([], 'simpr', '( %s -> %s <_ 8 )' % (ante, V))], 'jca',
                  '( %s -> ( %s /\\ %s <_ 8 ) )' % (ante, ZP, V))
        cl = w.s([low, w.inst('gamvbl')], 'syl', '( %s -> %s )' % (ante, GOAL))
    else:
        vr8 = w.s([w.s([w.s([zc], 'imcld', '( %s -> ( Im ` Z ) e. RR )' % ante)], 'recnd',
                       '( %s -> ( Im ` Z ) e. CC )' % ante)], 'abscld', '( %s -> %s e. RR )' % (ante, V))
        r8 = w.s([num.fact(w, '8', 'RR')], 'a1i', '( %s -> 8 e. RR )' % ante)
        lt = w.s([w.s([], 'simpr', '( %s -> -. %s <_ 8 )' % (ante, V)),
                  w.s([vr8, r8], 'lenltd', '( %s -> ( %s <_ 8 <-> -. 8 < %s ) )' % (ante, V, V))], 'jca', 'dummy')
        w.lines.pop()
        lt = w.s([r8, vr8, w.s([], 'simpr', '( %s -> -. %s <_ 8 )' % (ante, V))], 'ltnled', 'dummy')
        w.lines.pop()
        gt = w.s([w.s([], 'simpr', '( %s -> -. %s <_ 8 )' % (ante, V)),
                  w.s([vr8, r8], 'ltnled', '( %s -> ( 8 < %s <-> -. %s <_ 8 ) )' % (ante, V, V))], 'mpbird',
                 '( %s -> 8 < %s )' % (ante, V))
        ge = w.s([r8, vr8, gt], 'ltled', '( %s -> 8 <_ %s )' % (ante, V))
        hi = w.s([w.s([zp2, r3], 'jca', '( %s -> ( %s /\\ %s <_ 3 ) )' % (ante, ZP, RZ)), ge], 'jca',
                 '( %s -> ( ( %s /\\ %s <_ 3 ) /\\ 8 <_ %s ) )' % (ante, ZP, RZ, V))
        ch = w.s([hi, w.inst('gamvbh')], 'syl', '( %s -> %s )' % (ante, GOAL))
w.qed([cl, ch], 'pm2.61dan', '( %s -> %s )' % (AG, GOAL))
run4(w)
