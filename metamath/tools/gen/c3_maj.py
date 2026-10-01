"""Sortie C3 section 3: the coefficient majorant and the logarithm bound."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

# ---- logcxpbnd -------------------------------------------------------------
w = W('logcxpbnd', 'The logarithm is below any positive power, divided by the exponent.')
A0 = '( K e. NN /\\ E e. RR+ )'
kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
ep = w.s([erp], 'rpgt0d', '( %s -> 0 < E )' % A0)
ege = w.s([erp], 'rpge0d', '( %s -> 0 <_ E )' % A0)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0)
k1 = w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
ge01 = w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A0)
urp = w.s([krp, er, w.inst('rpcxpcl')], 'syl2anc', '( %s -> ( K ^c E ) e. RR+ )' % A0)
ur = w.s([urp], 'rpred', '( %s -> ( K ^c E ) e. RR )' % A0)
le1 = w.s([w.s([r1, kr, er], '3jca', '( %s -> ( 1 e. RR /\\ K e. RR /\\ E e. RR ) )' % A0),
           w.s([ge01, ege], 'jca', '( %s -> ( 0 <_ 1 /\\ 0 <_ E ) )' % A0), k1, w.inst('cxple2a')],
          'syl3anc', '( %s -> ( 1 ^c E ) <_ ( K ^c E ) )' % A0)
one = w.s([w.s([erp, w.inst('rpcnd')], 'syl', '( %s -> E e. CC )' % A0), w.inst('1cxp')], 'syl',
          '( %s -> ( 1 ^c E ) = 1 )' % A0)
u1 = w.s([one, le1], 'eqbrtrrd', '( %s -> 1 <_ ( K ^c E ) )' % A0)
lu = w.s([ur, u1, w.inst('loglet')], 'syl2anc', '( %s -> ( log ` ( K ^c E ) ) <_ ( K ^c E ) )' % A0)
lc = w.s([krp, er, w.inst('logcxp')], 'syl2anc', '( %s -> ( log ` ( K ^c E ) ) = ( E x. ( log ` K ) ) )' % A0)
mle = w.s([lc, lu], 'eqbrtrrd', '( %s -> ( E x. ( log ` K ) ) <_ ( K ^c E ) )' % A0)
lkr = w.s([krp, w.inst('relogcl')], 'syl', '( %s -> ( log ` K ) e. RR )' % A0)
bi = w.s([lkr, ur, w.s([er, ep], 'jca', '( %s -> ( E e. RR /\\ 0 < E ) )' % A0), w.inst('lemuldiv2')],
         'syl3anc', '( %s -> ( ( E x. ( log ` K ) ) <_ ( K ^c E ) <-> ( log ` K ) <_ ( ( K ^c E ) / E ) ) )' % A0)
w.qed([mle, bi], 'mpbid', '( %s -> ( log ` K ) <_ ( ( K ^c E ) / E ) )' % A0); run3(w)

# ---- dtmabs ----------------------------------------------------------------
w = W('dtmabs', 'The termwise majorant of a Dirichlet series with bounded coefficients.')
A0 = '( %s /\\ ( ( K e. NN /\\ T e. RR /\\ Z e. CC ) /\\ T <_ ( Re ` Z ) ) )' % CFB
af = w.s([], 'simpl1', '( %s -> A : NN --> CC )' % A0)
cr = w.s([], 'simpl2', '( %s -> C e. RR )' % A0)
ral = w.s([], 'simpl3', '( %s -> A. m e. NN ( abs ` ( A ` m ) ) <_ C )' % A0)
kn = w.s([], 'simprl1', '( %s -> K e. NN )' % A0)
tr = w.s([], 'simprl2', '( %s -> T e. RR )' % A0)
zc = w.s([], 'simprl3', '( %s -> Z e. CC )' % A0)
le = w.s([], 'simprr', '( %s -> T <_ ( Re ` Z ) )' % A0)
ak = w.s([af, kn], 'ffvelcdmd', '( %s -> ( A ` K ) e. CC )' % A0)
abk = w.s([ak], 'abscld', '( %s -> ( abs ` ( A ` K ) ) e. RR )' % A0)
ge0 = w.s([ak], 'absge0d', '( %s -> 0 <_ ( abs ` ( A ` K ) ) )' % A0)
# instantiate the coefficient bound at K
e1 = w.s([], 'fveq2', '( m = K -> ( A ` m ) = ( A ` K ) )')
e2 = w.s([e1], 'fveq2d', '( m = K -> ( abs ` ( A ` m ) ) = ( abs ` ( A ` K ) ) )')
e3 = w.s([e2], 'breq1d', '( m = K -> ( ( abs ` ( A ` m ) ) <_ C <-> ( abs ` ( A ` K ) ) <_ C ) )')
abkc = w.s([e3, ral, kn], 'rspcdva', '( %s -> ( abs ` ( A ` K ) ) <_ C )' % A0)
# the power factor
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
cz = w.s([w.s([krp, w.inst('rpcnd')], 'syl', '( %s -> K e. CC )' % A0),
          w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')], 'syl2anc',
         '( %s -> ( K ^c -u Z ) e. CC )' % A0)
abz = w.s([kn, zc, w.inst('cxpnnabs')], 'syl2anc', '( %s -> ( abs ` ( K ^c -u Z ) ) = ( K ^c -u ( Re ` Z ) ) )' % A0)
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> ( Re ` Z ) e. RR )' % A0)
nrzr = w.s([rz], 'renegcld', '( %s -> -u ( Re ` Z ) e. RR )' % A0)
ntr = w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)
zpr = w.s([krp, nrzr, w.inst('rpcxpcl')], 'syl2anc', '( %s -> ( K ^c -u ( Re ` Z ) ) e. RR+ )' % A0)
zprr = w.s([zpr], 'rpred', '( %s -> ( K ^c -u ( Re ` Z ) ) e. RR )' % A0)
tpr = w.s([krp, ntr, w.inst('rpcxpcl')], 'syl2anc', '( %s -> ( K ^c -u T ) e. RR+ )' % A0)
tprr = w.s([tpr], 'rpred', '( %s -> ( K ^c -u T ) e. RR )' % A0)
mono = w.s([w.s([kn, tr, zc], '3jca', '( %s -> ( K e. NN /\\ T e. RR /\\ Z e. CC ) )' % A0), le, w.inst('cxpnnle')],
           'syl2anc', '( %s -> ( K ^c -u ( Re ` Z ) ) <_ ( K ^c -u T ) )' % A0)
abzle = w.s([abz, mono], 'eqbrtrd', '( %s -> ( abs ` ( K ^c -u Z ) ) <_ ( K ^c -u T ) )' % A0)
abzr = w.s([cz], 'abscld', '( %s -> ( abs ` ( K ^c -u Z ) ) e. RR )' % A0)
abzg = w.s([cz], 'absge0d', '( %s -> 0 <_ ( abs ` ( K ^c -u Z ) ) )' % A0)
mul = w.s([abk, cr, abzr, tprr, ge0, abzg, abkc, abzle], 'lemul12ad',
          '( %s -> ( ( abs ` ( A ` K ) ) x. ( abs ` ( K ^c -u Z ) ) ) <_ ( C x. ( K ^c -u T ) ) )' % A0)
am = w.s([ak, cz], 'absmuld', '( %s -> ( abs ` ( ( A ` K ) x. ( K ^c -u Z ) ) ) = ( ( abs ` ( A ` K ) ) x. ( abs ` ( K ^c -u Z ) ) ) )' % A0)
w.qed([am, mul], 'eqbrtrd', '( %s -> ( abs ` ( ( A ` K ) x. ( K ^c -u Z ) ) ) <_ ( C x. ( K ^c -u T ) ) )' % A0); run3(w)
