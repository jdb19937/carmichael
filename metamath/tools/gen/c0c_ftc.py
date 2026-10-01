"""Sortie C0c batch 2: the reciprocal on the slit plane and its FTC."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

CC0 = '( CC \\ { 0 } )'
INV0 = '( x e. %s |-> ( 1 / x ) )' % CC0
LOGD = '( log |` %s )' % DD

# ---- slitss: the slit plane omits 0
w = W('slitss', 'The slit plane, the domain of the principal logarithm, omits zero.')
c1 = w.s([], 'eldifi', '( y e. %s -> y e. CC )' % DD)
e1 = w.s([], 'eqid', '%s = %s' % (DD, DD))
c2 = w.s([e1], 'logdmn0', '( y e. %s -> y =/= 0 )' % DD)
c3 = w.s([c1, c2], 'jca', '( y e. %s -> ( y e. CC /\\ y =/= 0 ) )' % DD)
c4 = w.s([], 'eldifsn', '( y e. %s <-> ( y e. CC /\\ y =/= 0 ) )' % CC0)
c5 = w.s([c3, c4], 'sylibr', '( y e. %s -> y e. %s )' % (DD, CC0))
w.qed([c5], 'ssriv', '%s C_ %s' % (DD, CC0)); run(w)

# ---- slitinvcn: the reciprocal is continuous on the slit plane
w = W('slitinvcn', 'The reciprocal is continuous on the slit plane, the domain of the principal logarithm.')
e1 = w.s([], 'eqid', '%s = %s' % (INV0, INV0))
c1 = w.s([e1], 'cdivcncf', '( 1 e. CC -> %s e. ( %s -cn-> CC ) )' % (INV0, CC0))
c2 = w.s([], 'ax-1cn', '1 e. CC')
c3 = w.s([c2, c1], 'ax-mp', '%s e. ( %s -cn-> CC )' % (INV0, CC0))
ss = w.s([], 'slitss', '%s C_ %s' % (DD, CC0))
c4 = w.s([ss, w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (INV0, CC0, INV0, DD, DD))
c5 = w.s([c3, c4], 'ax-mp', '( %s |` %s ) e. ( %s -cn-> CC )' % (INV0, DD, DD))
c6 = w.s([ss, w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (INV0, DD, INV))
w.qed([c6, c5], 'eqeltrri', '%s e. ( %s -cn-> CC )' % (INV, DD)); run(w)

# ---- lintrec: the FTC for 1 / x on a segment inside the slit plane
w = W('lintrec', 'The integral of the reciprocal along a segment of the slit plane is the difference of the principal logarithms of the endpoints.')
A0 = '( ( V e. CC /\\ W e. CC ) /\\ ( V cseg W ) C_ %s )' % DD
vc = w.s([], 'simpll', '( %s -> V e. CC )' % A0)
wc = w.s([], 'simplr', '( %s -> W e. CC )' % A0)
sg = w.s([], 'simpr', '( %s -> ( V cseg W ) C_ %s )' % (A0, DD))
e1 = w.s([], 'eqid', '%s = %s' % (DD, DD))
lcn = w.s([e1], 'logcn', '%s e. ( %s -cn-> CC )' % (LOGD, DD))
lf0 = w.s([lcn, w.inst('cncff')], 'ax-mp', '%s : %s --> CC' % (LOGD, DD))
lf = w.s([lf0], 'a1i', '( %s -> %s : %s --> CC )' % (A0, LOGD, DD))
e2 = w.s([], 'eqid', '%s = %s' % (DD, DD))
dv0 = w.s([e2], 'dvlog', '( CC _D %s ) = %s' % (LOGD, INV))
dv = w.s([dv0], 'a1i', '( %s -> ( CC _D %s ) = %s )' % (A0, LOGD, INV))
icn = closed(w, A0, 'slitinvcn', '%s e. ( %s -cn-> CC )' % (INV, DD))
h1 = w.s([vc, wc], 'jca', '( %s -> ( V e. CC /\\ W e. CC ) )' % A0)
h2 = w.s([lf, dv], 'jca', '( %s -> ( %s : %s --> CC /\\ ( CC _D %s ) = %s ) )' % (A0, LOGD, DD, LOGD, INV))
h3 = w.s([icn, sg], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( V cseg W ) C_ %s ) )' % (A0, INV, DD, DD))
ft = w.s([h1, h2, h3, w.inst('lintftc')], 'syl3anc', '( %s -> %s = ( ( %s ` W ) - ( %s ` V ) ) )' % (A0, LINT(INV, 'V', 'W'), LOGD, LOGD))
vd = w.s([sg, w.s([vc, wc, w.inst('csegid1')], 'syl2anc', '( %s -> V e. ( V cseg W ) )' % A0)], 'sseldd', '( %s -> V e. %s )' % (A0, DD))
wd = w.s([sg, w.s([vc, wc, w.inst('csegid2')], 'syl2anc', '( %s -> W e. ( V cseg W ) )' % A0)], 'sseldd', '( %s -> W e. %s )' % (A0, DD))
rv = w.s([vd, w.inst('fvres')], 'syl', '( %s -> ( %s ` V ) = ( log ` V ) )' % (A0, LOGD))
rw = w.s([wd, w.inst('fvres')], 'syl', '( %s -> ( %s ` W ) = ( log ` W ) )' % (A0, LOGD))
w.qed([ft, w.s([rw, rv], 'oveq12d', '( %s -> ( ( %s ` W ) - ( %s ` V ) ) = ( ( log ` W ) - ( log ` V ) ) )' % (A0, LOGD, LOGD))],
      'eqtrd', '( %s -> %s = ( ( log ` W ) - ( log ` V ) ) )' % (A0, LINT(INV, 'V', 'W'))); run(w)
