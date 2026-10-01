"""Sortie A2, batch 9: the exponential estimates of Step3W."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

FP = '( ~P Prime i^i Fin )'
A2 = '( ell2 ` N )'; A3 = '( ell3 ` N )'
SQ2 = '( %s ^ 2 )' % A2
ZR = '( ( C x. %s ) x. %s )' % (A2, A3)
CA = '( C x. %s )' % SQ2
E310 = '( exp ` ( ( 3 / ; 1 0 ) x. %s ) )' % A2

# -------------------------------------------------------------------- efcxp
w = W('efcxp', 'A real power of an exponential.')
A = '( X e. RR /\\ Y e. RR )'
xr = w.s([], 'simpl', '( %s -> X e. RR )' % A)
yr = w.s([], 'simpr', '( %s -> Y e. RR )' % A)
ex = w.s([xr], 'rpefcld', '( %s -> ( exp ` X ) e. RR+ )' % A)
exc = w.s([ex], 'rpcnd', '( %s -> ( exp ` X ) e. CC )' % A)
exn = w.s([ex], 'rpne0d', '( %s -> ( exp ` X ) =/= 0 )' % A)
yc = w.s([yr], 'recnd', '( %s -> Y e. CC )' % A)
ce = w.s([exc, exn, yc, w.inst('cxpef')], 'syl3anc', '( %s -> ( ( exp ` X ) ^c Y ) = ( exp ` ( Y x. ( log ` ( exp ` X ) ) ) ) )' % A)
rl = w.s([xr, w.inst('relogef')], 'syl', '( %s -> ( log ` ( exp ` X ) ) = X )' % A)
w.qed([ce, w.s([w.s([rl], 'oveq2d', '( %s -> ( Y x. ( log ` ( exp ` X ) ) ) = ( Y x. X ) )' % A)], 'fveq2d',
               '( %s -> ( exp ` ( Y x. ( log ` ( exp ` X ) ) ) ) = ( exp ` ( Y x. X ) ) )' % A)], 'eqtrd',
      '( %s -> ( ( exp ` X ) ^c Y ) = ( exp ` ( Y x. X ) ) )' % A)
run(w)

# ------------------------------------------------------------------ s3zp1exp
def ctx(w):
    d = {}
    d['cr'] = w.h('C e. RR')
    d['c1000'] = w.h('; ; ; 1 0 0 0 <_ C')
    d['n3'] = w.h('N e. ( ZZ>= ` 3 )')
    d['a50'] = w.h('; 5 0 <_ %s' % A2)
    d['b200'] = w.h('; ; 2 0 0 <_ %s' % A3)
    return d


def basics(w, d, A='ph'):
    d['n2'] = w.s([d['n3'], w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
    d['ar'] = w.s([d['n2'], w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, A2))
    d['br'] = w.s([d['n3'], w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, A3))
    LV = {'C': d['cr'], A2: d['ar'], A3: d['br']}
    d['c1'] = linarith(w, A, [d['c1000']], '1 <_ C', leaves=LV)
    d['c0'] = linarith(w, A, [d['c1000']], '0 <_ C', leaves=LV)
    d['a1'] = linarith(w, A, [d['a50']], '1 <_ %s' % A2, leaves=LV)
    d['a0'] = linarith(w, A, [d['a50']], '0 <_ %s' % A2, leaves=LV)
    d['blea'] = w.s([d['n3'], w.inst('ell3lt')], 'syl', '( %s -> %s < %s )' % (A, A3, A2))
    d['bleae'] = w.s([d['blea']], 'ltled', '( %s -> %s <_ %s )' % (A, A3, A2))
    d['sqr'] = w.s([d['ar']], 'resqcld', '( %s -> %s e. RR )' % (A, SQ2))
    d['sq0'] = w.s([d['ar']], 'sqge0d', '( %s -> 0 <_ %s )' % (A, SQ2))
    d['sq1'] = w.s([d['ar'], w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), d['a1']], 'expge1d',
                   '( %s -> 1 <_ %s )' % (A, SQ2))
    d['car'] = w.s([d['cr'], d['sqr']], 'remulcld', '( %s -> %s e. RR )' % (A, CA))
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    l12 = w.s([one, d['cr'], one, d['sqr'],
               w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A),
               w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A),
               d['c1'], d['sq1']], 'lemul12ad', '( %s -> ( 1 x. 1 ) <_ %s )' % (A, CA))
    t11 = w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % A)
    d['ca1'] = w.s([w.s([t11], 'eqcomd', '( %s -> 1 = ( 1 x. 1 ) )' % A), l12], 'eqbrtrd', '( %s -> 1 <_ %s )' % (A, CA))
    return d


w = WH('s3zp1exp', 'z + 1 is below exp ( ( 3 / 10 ) ell2 n ) at windowed scales (Lean: Step3W.lean hzp1_exp).')
d = ctx(w)
zn0 = w.h('Z e. NN0')
zhi = w.h('Z <_ ( 4 x. %s )' % ZR)
kr = w.h('K e. RR')
k5 = w.h('( 5 x. C ) <_ K')
kq = w.h('( K x. %s ) <_ %s' % (SQ2, E310))
basics(w, d)
A = 'ph'
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
ac = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A, A2))
bc = w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A, A3))
cc_ = w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A)
c4 = w.s([w.s([], '4cn', '4 e. CC')], 'a1i', '( %s -> 4 e. CC )' % A)
cas = w.s([d['cr'], d['ar']], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (A, A2))
ca0 = w.s([d['cr'], d['ar'], d['c0'], d['a0']], 'mulge0d', '( %s -> 0 <_ ( C x. %s ) )' % (A, A2))
m1 = w.s([d['br'], d['ar'], cas, ca0, d['bleae']], 'lemul2ad', '( %s -> %s <_ ( ( C x. %s ) x. %s ) )' % (A, ZR, A2, A2))
# ( ( C x. a ) x. a ) = CA  and  ( 4 x. ZR ) <_ ( 4 x. CA )
e1 = w.s([cc_, ac, ac], 'mulassd', '( %s -> ( ( C x. %s ) x. %s ) = ( C x. ( %s x. %s ) ) )' % (A, A2, A2, A2, A2))
sv = w.s([ac], 'sqvald', '( %s -> %s = ( %s x. %s ) )' % (A, SQ2, A2, A2))
e2 = w.s([e1, w.s([w.s([sv], 'eqcomd', '( %s -> ( %s x. %s ) = %s )' % (A, A2, A2, SQ2))], 'oveq2d',
                  '( %s -> ( C x. ( %s x. %s ) ) = %s )' % (A, A2, A2, CA))], 'eqtrd',
         '( %s -> ( ( C x. %s ) x. %s ) = %s )' % (A, A2, A2, CA))
m2 = w.s([m1, e2], 'breqtrd', '( %s -> %s <_ %s )' % (A, ZR, CA))
zrr = w.s([cas, d['br']], 'remulcld', '( %s -> %s e. RR )' % (A, ZR))
m3 = linarith(w, A, [zhi, m2], 'Z <_ ( 4 x. %s )' % CA, leaves={'Z': zr, ZR: zrr, CA: d['car']})
zp5 = linarith(w, A, [m3, d['ca1']], '( Z + 1 ) <_ ( 5 x. %s )' % CA, leaves={'Z': zr, CA: d['car']})
# ( 5 x. CA ) = ( 5 x. C ) x. SQ2 <_ K x. SQ2
c5 = w.s([w.s([], '5cn', '5 e. CC')], 'a1i', '( %s -> 5 e. CC )' % A)
sqc = w.s([d['sqr']], 'recnd', '( %s -> %s e. CC )' % (A, SQ2))
e3 = w.s([c5, cc_, sqc], 'mulassd', '( %s -> ( ( 5 x. C ) x. %s ) = ( 5 x. %s ) )' % (A, SQ2, CA))
f5c = w.s([w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % A), d['cr']], 'remulcld', '( %s -> ( 5 x. C ) e. RR )' % A)
m4 = w.s([f5c, kr, d['sqr'], d['sq0'], k5], 'lemul1ad', '( %s -> ( ( 5 x. C ) x. %s ) <_ ( K x. %s ) )' % (A, SQ2, SQ2))
m5 = w.s([w.s([e3], 'eqcomd', '( %s -> ( 5 x. %s ) = ( ( 5 x. C ) x. %s ) )' % (A, CA, SQ2)), m4], 'eqbrtrd',
         '( %s -> ( 5 x. %s ) <_ ( K x. %s ) )' % (A, CA, SQ2))
ksq = w.s([kr, d['sqr']], 'remulcld', '( %s -> ( K x. %s ) e. RR )' % (A, SQ2))
er = w.s([w.s([w.s([num.fact(w, '( 3 / ; 1 0 )', 'RR')], 'a1i', '( %s -> ( 3 / ; 1 0 ) e. RR )' % A), d['ar']], 'remulcld',
             '( %s -> ( ( 3 / ; 1 0 ) x. %s ) e. RR )' % (A, A2))], 'reefcld', '( %s -> %s e. RR )' % (A, E310))
zp1r = w.s([zr, w.s([], '1red', '( %s -> 1 e. RR )' % A)], 'readdcld', '( %s -> ( Z + 1 ) e. RR )' % A)
c5a = w.s([w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % A), d['car']], 'remulcld', '( %s -> ( 5 x. %s ) e. RR )' % (A, CA))
t1 = w.s([zp1r, c5a, ksq, zp5, m5], 'letrd', '( %s -> ( Z + 1 ) <_ ( K x. %s ) )' % (A, SQ2))
w.qed([zp1r, ksq, er, t1, kq], 'letrd', '( %s -> ( Z + 1 ) <_ %s )' % (A, E310))
run(w)

# ------------------------------------------------------------------- s3twot
w = WH('s3twot', 'exp ( ( 3 / 2 ) A ) <_ 2 ^ T when 3 A <_ T (Lean: Step3W.lean h2T_ge, with log 2 >_ 1 / 2).')
tn0 = w.h('T e. NN0'); ar = w.h('A e. RR'); a0 = w.h('0 <_ A'); t3 = w.h('( 3 x. A ) <_ T')
B = 'ph'
tr = w.s([tn0], 'nn0red', '( %s -> T e. RR )' % B)
tz = w.s([tn0], 'nn0zd', '( %s -> T e. ZZ )' % B)
tg0 = w.s([tn0], 'nn0ge0d', '( %s -> 0 <_ T )' % B)
r2 = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % B)
re = w.s([r2, tz, w.inst('reexplog')], 'syl2anc', '( %s -> ( 2 ^ T ) = ( exp ` ( T x. ( log ` 2 ) ) ) )' % B)
l2r = w.s([r2, w.inst('relogcl')], 'syl', '( %s -> ( log ` 2 ) e. RR )' % B)
l2g = w.s([w.s([], 'log2ge', '( 1 / 2 ) <_ ( log ` 2 )')], 'a1i', '( %s -> ( 1 / 2 ) <_ ( log ` 2 ) )' % B)
h12 = w.s([num.fact(w, '( 1 / 2 )', 'RR')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % B)
m1 = w.s([h12, l2r, tr, tg0, l2g], 'lemul2ad', '( %s -> ( T x. ( 1 / 2 ) ) <_ ( T x. ( log ` 2 ) ) )' % B)
tl2 = w.s([tr, l2r], 'remulcld', '( %s -> ( T x. ( log ` 2 ) ) e. RR )' % B)
lin = linarith(w, B, [m1, t3, a0], '( ( 3 / 2 ) x. A ) <_ ( T x. ( log ` 2 ) )',
               leaves={'A': ar, 'T': tr, '( T x. ( log ` 2 ) )': tl2})
h32 = w.s([num.fact(w, '( 3 / 2 )', 'RR')], 'a1i', '( %s -> ( 3 / 2 ) e. RR )' % B)
lhs = w.s([h32, ar], 'remulcld', '( %s -> ( ( 3 / 2 ) x. A ) e. RR )' % B)
bi = w.s([lhs, tl2, w.inst('efle')], 'syl2anc',
         '( %s -> ( ( ( 3 / 2 ) x. A ) <_ ( T x. ( log ` 2 ) ) <-> ( exp ` ( ( 3 / 2 ) x. A ) ) <_ ( exp ` ( T x. ( log ` 2 ) ) ) ) )' % B)
ef = w.s([lin, bi], 'mpbid', '( %s -> ( exp ` ( ( 3 / 2 ) x. A ) ) <_ ( exp ` ( T x. ( log ` 2 ) ) ) )' % B)
w.qed([ef, w.s([re], 'eqcomd', '( %s -> ( exp ` ( T x. ( log ` 2 ) ) ) = ( 2 ^ T ) )' % B)], 'breqtrd',
      '( %s -> ( exp ` ( ( 3 / 2 ) x. A ) ) <_ ( 2 ^ T ) )' % B)
run(w)

# ----------------------------------------------------------------- q579200
w = W('q579200', '5 x. ( 79 / 200 ) = 79 / 40 .')
c5 = num.fact(w, '5', 'CC'); c79 = num.fact(w, '; 7 9', 'CC')
c200 = num.fact(w, '; ; 2 0 0', 'CC'); n200 = num.fact(w, '; ; 2 0 0', 'ne0')
c40 = num.fact(w, '; 4 0', 'CC'); n40 = num.fact(w, '; 4 0', 'ne0'); n5 = num.fact(w, '5', 'ne0')
da = w.s([c5, c79, w.s([c200, n200], 'pm3.2i', '( ; ; 2 0 0 e. CC /\\ ; ; 2 0 0 =/= 0 )'), w.inst('divass')], 'mp3an',
         '( ( 5 x. ; 7 9 ) / ; ; 2 0 0 ) = ( 5 x. ( ; 7 9 / ; ; 2 0 0 ) )')
m1 = num.mul_nat(w, 5, 79)
m2 = num.mul_nat(w, 5, 40)
dc = w.s([c79, w.s([c40, n40], 'pm3.2i', '( ; 4 0 e. CC /\\ ; 4 0 =/= 0 )'),
          w.s([c5, n5], 'pm3.2i', '( 5 e. CC /\\ 5 =/= 0 )'), w.inst('divcan5')], 'mp3an',
         '( ( 5 x. ; 7 9 ) / ( 5 x. ; 4 0 ) ) = ( ; 7 9 / ; 4 0 )')
e1 = w.s([m2], 'oveq2i', '( ( 5 x. ; 7 9 ) / ( 5 x. ; 4 0 ) ) = ( ( 5 x. ; 7 9 ) / ; ; 2 0 0 )')
e2 = w.s([w.s([e1], 'eqcomi', '( ( 5 x. ; 7 9 ) / ; ; 2 0 0 ) = ( ( 5 x. ; 7 9 ) / ( 5 x. ; 4 0 ) )'), dc], 'eqtri',
         '( ( 5 x. ; 7 9 ) / ; ; 2 0 0 ) = ( ; 7 9 / ; 4 0 )')
w.qed([w.s([da], 'eqcomi', '( 5 x. ( ; 7 9 / ; ; 2 0 0 ) ) = ( ( 5 x. ; 7 9 ) / ; ; 2 0 0 )'), e2], 'eqtri',
      '( 5 x. ( ; 7 9 / ; ; 2 0 0 ) ) = ( ; 7 9 / ; 4 0 )')
run(w)

# --------------------------------------------------------------------- s3qb
GPW = '( ( Z goodPrimesW W ) ` Y )'
TY = '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'
LS = '( Lmod ` S )'; XCS = '( xceil ` S )'
Q79 = '( ; 7 9 / ; ; 2 0 0 )'; Q7940 = '( ; 7 9 / ; 4 0 )'
PRD = '{ p e. Prime | p || %s }' % LS

w = WH('s3qb', 'Every prime factor of L = Lmod Q is at most x ^ ( 79 / 200 ) (Lean: Step3W.lean hqbound).')
sfp = w.h('S e. %s' % FP)
hc = w.h('( # ` S ) = T')
zn0 = w.h('Z e. NN0'); wn0 = w.h('W e. NN0'); yn0 = w.h('Y e. NN0')
sub = w.h('S C_ %s' % GPW)
ar = w.h('A e. RR'); a0 = w.h('0 <_ A'); t3 = w.h('( 3 x. A ) <_ T')
zle = w.h('Z <_ ( exp ` ( ( 3 / ; 1 0 ) x. A ) )')
B = 'ph'
sfi = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B)], 'simprd', '( %s -> S e. Fin )' % B)
tn0 = w.s([hc, w.s([sfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % B)], 'eqeltrrd', '( %s -> T e. NN0 )' % B)
lnn = w.s([sfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (B, LS))
lrp = w.s([lnn], 'nnrpd', '( %s -> %s e. RR+ )' % (B, LS))
lr = w.s([lnn], 'nnred', '( %s -> %s e. RR )' % (B, LS))
l1 = w.s([lnn], 'nnge1d', '( %s -> 1 <_ %s )' % (B, LS))
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B)], 'simpld', '( %s -> S C_ Prime )' % B)
pn0 = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % B)], 'sstrd', '( %s -> S C_ NN0 )' % B)
sfn0 = w.s([w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % B), w.inst('elfpw')], 'sylibr',
           '( %s -> S e. ( ~P NN0 i^i Fin ) )' % B)
xv = w.s([sfn0, w.inst('xceilval')], 'syl', '( %s -> %s = ( %s ^ 5 ) )' % (B, XCS, LS))
lb = w.s([sfp, w.inst('prmprodlb')], 'syl', '( %s -> ( 2 ^ ( # ` S ) ) <_ %s )' % (B, LS))
lb2 = w.s([w.s([w.s([hc], 'oveq2d', '( %s -> ( 2 ^ ( # ` S ) ) = ( 2 ^ T ) )' % B)], 'eqcomd',
               '( %s -> ( 2 ^ T ) = ( 2 ^ ( # ` S ) ) )' % B), lb], 'eqbrtrd', '( %s -> ( 2 ^ T ) <_ %s )' % (B, LS))
tw = w.s([tn0, ar, a0, t3], 's3twot', '( %s -> ( exp ` ( ( 3 / 2 ) x. A ) ) <_ ( 2 ^ T ) )' % B)
# Z <_ exp ( ( 3 / 10 ) A ) <_ exp ( ( 3 / 2 ) A ) <_ 2 ^ T <_ L
h310 = w.s([num.fact(w, '( 3 / ; 1 0 )', 'RR')], 'a1i', '( %s -> ( 3 / ; 1 0 ) e. RR )' % B)
h32 = w.s([num.fact(w, '( 3 / 2 )', 'RR')], 'a1i', '( %s -> ( 3 / 2 ) e. RR )' % B)
e1r = w.s([h310, ar], 'remulcld', '( %s -> ( ( 3 / ; 1 0 ) x. A ) e. RR )' % B)
e2r = w.s([h32, ar], 'remulcld', '( %s -> ( ( 3 / 2 ) x. A ) e. RR )' % B)
lex = linarith(w, B, [a0], '( ( 3 / ; 1 0 ) x. A ) <_ ( ( 3 / 2 ) x. A )', leaves={'A': ar})
bi = w.s([e1r, e2r, w.inst('efle')], 'syl2anc',
         '( %s -> ( ( ( 3 / ; 1 0 ) x. A ) <_ ( ( 3 / 2 ) x. A ) <-> ( exp ` ( ( 3 / ; 1 0 ) x. A ) ) <_ ( exp ` ( ( 3 / 2 ) x. A ) ) ) )' % B)
efm = w.s([lex, bi], 'mpbid', '( %s -> ( exp ` ( ( 3 / ; 1 0 ) x. A ) ) <_ ( exp ` ( ( 3 / 2 ) x. A ) ) )' % B)
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % B)
ef1 = w.s([e1r], 'reefcld', '( %s -> ( exp ` ( ( 3 / ; 1 0 ) x. A ) ) e. RR )' % B)
ef2 = w.s([e2r], 'reefcld', '( %s -> ( exp ` ( ( 3 / 2 ) x. A ) ) e. RR )' % B)
t2r = w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % B), tn0], 'nnexpcld', '( %s -> ( 2 ^ T ) e. NN )' % B)
t2re = w.s([t2r], 'nnred', '( %s -> ( 2 ^ T ) e. RR )' % B)
c1 = w.s([zr, ef1, ef2, zle, efm], 'letrd', '( %s -> Z <_ ( exp ` ( ( 3 / 2 ) x. A ) ) )' % B)
c2 = w.s([zr, ef2, t2re, c1, tw], 'letrd', '( %s -> Z <_ ( 2 ^ T ) )' % B)
zlel = w.s([zr, t2re, lr, c2, lb2], 'letrd', '( %s -> Z <_ %s )' % (B, LS))
# L <_ L ^c ( 79 / 40 ) = x ^c ( 79 / 200 )
q7 = w.s([num.fact(w, Q7940, 'RR')], 'a1i', '( %s -> %s e. RR )' % (B, Q7940))
one = w.s([], '1red', '( %s -> 1 e. RR )' % B)
le1 = linarith(w, B, [], '1 <_ %s' % Q7940, leaves={})
cx = w.s([lr, l1, one, q7, le1], 'cxplead', '( %s -> ( %s ^c 1 ) <_ ( %s ^c %s ) )' % (B, LS, LS, Q7940))
c1e = w.s([w.s([lr], 'recnd', '( %s -> %s e. CC )' % (B, LS))], 'cxp1d', '( %s -> ( %s ^c 1 ) = %s )' % (B, LS, LS))
lle = w.s([w.s([c1e], 'eqcomd', '( %s -> %s = ( %s ^c 1 ) )' % (B, LS, LS)), cx], 'eqbrtrd',
          '( %s -> %s <_ ( %s ^c %s ) )' % (B, LS, LS, Q7940))
# x ^c ( 79 / 200 ) = L ^c ( 79 / 40 )
q79r = w.s([num.fact(w, Q79, 'RR')], 'a1i', '( %s -> %s e. RR )' % (B, Q79))
q79c = w.s([q79r], 'recnd', '( %s -> %s e. CC )' % (B, Q79))
r5 = w.s([num.fact(w, '5', 'RR')], 'a1i', '( %s -> 5 e. RR )' % B)
cm = w.s([lrp, r5, q79c, w.inst('cxpmul')], 'syl3anc', '( %s -> ( %s ^c ( 5 x. %s ) ) = ( ( %s ^c 5 ) ^c %s ) )' % (B, LS, Q79, LS, Q79))
ce = w.s([w.s([lr], 'recnd', '( %s -> %s e. CC )' % (B, LS)), w.s([num.fact(w, '5', 'NN0')], 'a1i', '( %s -> 5 e. NN0 )' % B),
          w.inst('cxpexp')], 'syl2anc', '( %s -> ( %s ^c 5 ) = ( %s ^ 5 ) )' % (B, LS, LS))
q5 = w.s([w.s([], 'q579200', '( 5 x. %s ) = %s' % (Q79, Q7940))], 'a1i', '( %s -> ( 5 x. %s ) = %s )' % (B, Q79, Q7940))
lhs = w.s([w.s([q5], 'oveq2d', '( %s -> ( %s ^c ( 5 x. %s ) ) = ( %s ^c %s ) )' % (B, LS, Q79, LS, Q7940))], 'eqcomd',
          '( %s -> ( %s ^c %s ) = ( %s ^c ( 5 x. %s ) ) )' % (B, LS, Q7940, LS, Q79))
rhs = w.s([cm, w.s([ce], 'oveq1d', '( %s -> ( ( %s ^c 5 ) ^c %s ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, LS, Q79, LS, Q79))], 'eqtrd',
          '( %s -> ( %s ^c ( 5 x. %s ) ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, LS, Q79, LS, Q79))
xeq = w.s([w.s([xv], 'oveq1d', '( %s -> ( %s ^c %s ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, XCS, Q79, LS, Q79))], 'eqcomd',
          '( %s -> ( ( %s ^ 5 ) ^c %s ) = ( %s ^c %s ) )' % (B, LS, Q79, XCS, Q79))
tot = w.s([w.s([lhs, rhs], 'eqtrd', '( %s -> ( %s ^c %s ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, LS, Q7940, LS, Q79)), xeq], 'eqtrd',
          '( %s -> ( %s ^c %s ) = ( %s ^c %s ) )' % (B, LS, Q7940, XCS, Q79))
lle2 = w.s([lle, tot], 'breqtrd', '( %s -> %s <_ ( %s ^c %s ) )' % (B, LS, XCS, Q79))
totr = w.s([tot], 'eqcomd', '( %s -> ( %s ^c %s ) = ( %s ^c %s ) )' % (B, XCS, Q79, LS, Q7940))
lge0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % B), one, lr, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % B), l1], 'letrd', '( %s -> 0 <_ %s )' % (B, LS))
lcx7 = w.s([lr, lge0, q7], 'recxpcld', '( %s -> ( %s ^c %s ) e. RR )' % (B, LS, Q7940))
xcre = w.s([totr, lcx7], 'eqeltrd', '( %s -> ( %s ^c %s ) e. RR )' % (B, XCS, Q79))
zq = w.s([zr, lr, xcre, zlel, lle2], 'letrd', '( %s -> Z <_ ( %s ^c %s ) )' % (B, XCS, Q79))
# every prime factor of L is in S, hence at most Z
ps = w.s([sfp, w.inst('prmprodset')], 'syl', '( %s -> %s = S )' % (B, PRD))
ty = w.s([zn0, wn0, yn0], '3jca', '( %s -> %s )' % (B, TY))
allz = w.s([w.s([ty, sub], 'jca', '( %s -> ( %s /\\ S C_ %s ) )' % (B, TY, GPW)), w.inst('s3sallz')], 'syl',
           '( %s -> A. p e. S p <_ Z )' % B)
D = '( %s /\\ q e. Prime )' % B
E = '( %s /\\ q || %s )' % (D, LS)
idp = w.s([], 'id', '( p = q -> p = q )')
cgl, _b = w.wcongr('p || %s' % LS, {'p': 'q'}, 'p = q', {'p': idp})
elr = w.s([cgl], 'elrab', '( q e. %s <-> ( q e. Prime /\\ q || %s ) )' % (PRD, LS))
mem = w.s([w.s([w.s([], 'simplr', '( %s -> q e. Prime )' % E), w.s([], 'simpr', '( %s -> q || %s )' % (E, LS))], 'jca',
               '( %s -> ( q e. Prime /\\ q || %s ) )' % (E, LS)),
           w.s([elr], 'a1i', '( %s -> ( q e. %s <-> ( q e. Prime /\\ q || %s ) ) )' % (E, PRD, LS))], 'mpbird',
          '( %s -> q e. %s )' % (E, PRD))
inS = w.s([mem, w.s([ps], 'ad2antrr', '( %s -> %s = S )' % (E, PRD))], 'eleqtrd', '( %s -> q e. S )' % E)
cgz, _b2 = w.wcongr('p <_ Z', {'p': 'q'}, 'p = q', {'p': idp})
qlez = w.s([cgz, w.s([allz], 'ad2antrr', '( %s -> A. p e. S p <_ Z )' % E), inS], 'rspcdva', '( %s -> q <_ Z )' % E)
qre = w.s([w.s([w.s([], 'simplr', '( %s -> q e. Prime )' % E), w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % E)], 'nnred',
          '( %s -> q e. RR )' % E)
qq = w.s([qre, w.s([zr], 'ad2antrr', '( %s -> Z e. RR )' % E), w.s([xcre], 'ad2antrr', '( %s -> ( %s ^c %s ) e. RR )' % (E, XCS, Q79)),
          qlez, w.s([zq], 'ad2antrr', '( %s -> Z <_ ( %s ^c %s ) )' % (E, XCS, Q79))], 'letrd',
         '( %s -> q <_ ( %s ^c %s ) )' % (E, XCS, Q79))
imp = w.s([qq], 'ex', '( %s -> ( q || %s -> q <_ ( %s ^c %s ) ) )' % (D, LS, XCS, Q79))
w.qed([imp], 'ralrimiva', '( %s -> A. q e. Prime ( q || %s -> q <_ ( %s ^c %s ) ) )' % (B, LS, XCS, Q79))
run(w)

# ------------------------------------------------------------------ q31065
w = W('q31065', '( 3 / 10 ) + ( 6 / 5 ) = 3 / 2 .')
c2 = num.fact(w, '2', 'CC'); n2 = num.fact(w, '2', 'ne0')
c5 = num.fact(w, '5', 'CC'); n5 = num.fact(w, '5', 'ne0')
c6 = num.fact(w, '6', 'CC'); c3 = num.fact(w, '3', 'CC')
c10 = num.fact(w, '; 1 0', 'CC'); n10 = num.fact(w, '; 1 0', 'ne0')
c12 = num.fact(w, '; 1 2', 'CC')
j5 = w.s([c5, n5], 'pm3.2i', '( 5 e. CC /\\ 5 =/= 0 )')
j2 = w.s([c2, n2], 'pm3.2i', '( 2 e. CC /\\ 2 =/= 0 )')
j10 = w.s([c10, n10], 'pm3.2i', '( ; 1 0 e. CC /\\ ; 1 0 =/= 0 )')
d1 = w.s([c6, j5, j2, w.inst('divcan5')], 'mp3an', '( ( 2 x. 6 ) / ( 2 x. 5 ) ) = ( 6 / 5 )')
m26 = num.mul_nat(w, 2, 6); m25 = num.mul_nat(w, 2, 5)
d1b = w.s([m26, m25], 'oveq12i', '( ( 2 x. 6 ) / ( 2 x. 5 ) ) = ( ; 1 2 / ; 1 0 )')
e65 = w.s([w.s([d1b], 'eqcomi', '( ; 1 2 / ; 1 0 ) = ( ( 2 x. 6 ) / ( 2 x. 5 ) )'), d1], 'eqtri', '( ; 1 2 / ; 1 0 ) = ( 6 / 5 )')
dd = w.s([c3, c12, j10, w.inst('divdir')], 'mp3an', '( ( 3 + ; 1 2 ) / ; 1 0 ) = ( ( 3 / ; 1 0 ) + ( ; 1 2 / ; 1 0 ) )')
a312 = num.add_nat(w, 3, 12)
dd2 = w.s([w.s([a312], 'oveq1i', '( ( 3 + ; 1 2 ) / ; 1 0 ) = ( ; 1 5 / ; 1 0 )')], 'eqcomi', '( ; 1 5 / ; 1 0 ) = ( ( 3 + ; 1 2 ) / ; 1 0 )')
d2 = w.s([c3, j2, j5, w.inst('divcan5')], 'mp3an', '( ( 5 x. 3 ) / ( 5 x. 2 ) ) = ( 3 / 2 )')
m53 = num.mul_nat(w, 5, 3); m52 = num.mul_nat(w, 5, 2)
d2b = w.s([m53, m52], 'oveq12i', '( ( 5 x. 3 ) / ( 5 x. 2 ) ) = ( ; 1 5 / ; 1 0 )')
e32 = w.s([w.s([d2b], 'eqcomi', '( ; 1 5 / ; 1 0 ) = ( ( 5 x. 3 ) / ( 5 x. 2 ) )'), d2], 'eqtri', '( ; 1 5 / ; 1 0 ) = ( 3 / 2 )')
lhs = w.s([w.s([dd2, dd], 'eqtri', '( ; 1 5 / ; 1 0 ) = ( ( 3 / ; 1 0 ) + ( ; 1 2 / ; 1 0 ) )'),
           w.s([e65], 'oveq2i', '( ( 3 / ; 1 0 ) + ( ; 1 2 / ; 1 0 ) ) = ( ( 3 / ; 1 0 ) + ( 6 / 5 ) )')], 'eqtri',
          '( ; 1 5 / ; 1 0 ) = ( ( 3 / ; 1 0 ) + ( 6 / 5 ) )')
w.qed([w.s([lhs], 'eqcomi', '( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) = ( ; 1 5 / ; 1 0 )'), e32], 'eqtri',
      '( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) = ( 3 / 2 )')
run(w)

# ------------------------------------------------------------------ q521100
w = W('q521100', '5 x. ( 21 / 100 ) = 21 / 20 .')
c5 = num.fact(w, '5', 'CC'); n5 = num.fact(w, '5', 'ne0')
c21 = num.fact(w, '; 2 1', 'CC')
c100 = num.fact(w, '; ; 1 0 0', 'CC'); n100 = num.fact(w, '; ; 1 0 0', 'ne0')
c20 = num.fact(w, '; 2 0', 'CC'); n20 = num.fact(w, '; 2 0', 'ne0')
da = w.s([c5, c21, w.s([c100, n100], 'pm3.2i', '( ; ; 1 0 0 e. CC /\\ ; ; 1 0 0 =/= 0 )'), w.inst('divass')], 'mp3an',
         '( ( 5 x. ; 2 1 ) / ; ; 1 0 0 ) = ( 5 x. ( ; 2 1 / ; ; 1 0 0 ) )')
m1 = num.mul_nat(w, 5, 21); m2 = num.mul_nat(w, 5, 20)
dc = w.s([c21, w.s([c20, n20], 'pm3.2i', '( ; 2 0 e. CC /\\ ; 2 0 =/= 0 )'),
          w.s([c5, n5], 'pm3.2i', '( 5 e. CC /\\ 5 =/= 0 )'), w.inst('divcan5')], 'mp3an',
         '( ( 5 x. ; 2 1 ) / ( 5 x. ; 2 0 ) ) = ( ; 2 1 / ; 2 0 )')
e1 = w.s([m2], 'oveq2i', '( ( 5 x. ; 2 1 ) / ( 5 x. ; 2 0 ) ) = ( ( 5 x. ; 2 1 ) / ; ; 1 0 0 )')
e2 = w.s([w.s([e1], 'eqcomi', '( ( 5 x. ; 2 1 ) / ; ; 1 0 0 ) = ( ( 5 x. ; 2 1 ) / ( 5 x. ; 2 0 ) )'), dc], 'eqtri',
         '( ( 5 x. ; 2 1 ) / ; ; 1 0 0 ) = ( ; 2 1 / ; 2 0 )')
w.qed([w.s([da], 'eqcomi', '( 5 x. ( ; 2 1 / ; ; 1 0 0 ) ) = ( ( 5 x. ; 2 1 ) / ; ; 1 0 0 )'), e2], 'eqtri',
      '( 5 x. ( ; 2 1 / ; ; 1 0 0 ) ) = ( ; 2 1 / ; 2 0 )')
run(w)

# ------------------------------------------------------------------- s3thr
w = WH('s3thr', 'The AGP threshold z3 is below x = ( Lmod Q ) ^ 5 (Lean: Step3W.lean hz3x).')
sfp = w.h('S e. %s' % FP)
hc = w.h('( # ` S ) = T')
xn0 = w.h('X e. NN0'); ar = w.h('A e. RR'); a0 = w.h('0 <_ A')
xa = w.h('X <_ A'); t3 = w.h('( 3 x. A ) <_ T')
B = 'ph'
sfi = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B)], 'simprd', '( %s -> S e. Fin )' % B)
tn0 = w.s([hc, w.s([sfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % B)], 'eqeltrrd', '( %s -> T e. NN0 )' % B)
lnn = w.s([sfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (B, LS))
lr = w.s([lnn], 'nnred', '( %s -> %s e. RR )' % (B, LS))
l1 = w.s([lnn], 'nnge1d', '( %s -> 1 <_ %s )' % (B, LS))
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B)], 'simpld', '( %s -> S C_ Prime )' % B)
pn0 = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % B)], 'sstrd', '( %s -> S C_ NN0 )' % B)
sfn0 = w.s([w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % B), w.inst('elfpw')], 'sylibr',
           '( %s -> S e. ( ~P NN0 i^i Fin ) )' % B)
xv = w.s([sfn0, w.inst('xceilval')], 'syl', '( %s -> %s = ( %s ^ 5 ) )' % (B, XCS, LS))
tr = w.s([tn0], 'nn0red', '( %s -> T e. RR )' % B)
xr = w.s([xn0], 'nn0red', '( %s -> X e. RR )' % B)
xt = linarith(w, B, [xa, t3, a0], 'X <_ T', leaves={'X': xr, 'A': ar, 'T': tr})
uz2 = w.s([num.fact(w, '2', 'ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % B)
tlt = w.s([w.s([uz2, w.inst('uzid')], 'syl', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % B),
           tn0, w.inst('bernneq3')], 'syl2anc', '( %s -> T < ( 2 ^ T ) )' % B)
lb = w.s([sfp, w.inst('prmprodlb')], 'syl', '( %s -> ( 2 ^ ( # ` S ) ) <_ %s )' % (B, LS))
lb2 = w.s([w.s([w.s([hc], 'oveq2d', '( %s -> ( 2 ^ ( # ` S ) ) = ( 2 ^ T ) )' % B)], 'eqcomd',
               '( %s -> ( 2 ^ T ) = ( 2 ^ ( # ` S ) ) )' % B), lb], 'eqbrtrd', '( %s -> ( 2 ^ T ) <_ %s )' % (B, LS))
z5uz = w.s([w.s([], '5nn0', '5 e. NN0')], 'a1i', '( %s -> 5 e. NN0 )' % B)
n5uc = w.s([w.s([], '5nn', '5 e. NN'), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtri', '5 e. ( ZZ>= ` 1 )')
n5u = w.s([n5uc], 'a1i', '( %s -> 5 e. ( ZZ>= ` 1 ) )' % B)
le5 = w.s([lr, l1, n5u, w.inst('leexp2a')], 'syl3anc', '( %s -> ( %s ^ 1 ) <_ ( %s ^ 5 ) )' % (B, LS, LS))
e1 = w.s([w.s([lr], 'recnd', '( %s -> %s e. CC )' % (B, LS))], 'exp1d', '( %s -> ( %s ^ 1 ) = %s )' % (B, LS, LS))
le5b = w.s([w.s([e1], 'eqcomd', '( %s -> %s = ( %s ^ 1 ) )' % (B, LS, LS)), le5], 'eqbrtrd', '( %s -> %s <_ ( %s ^ 5 ) )' % (B, LS, LS))
l5r = w.s([lr, z5uz], 'reexpcld', '( %s -> ( %s ^ 5 ) e. RR )' % (B, LS))
t2r = w.s([w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % B), tn0], 'nnexpcld', '( %s -> ( 2 ^ T ) e. NN )' % B)], 'nnred',
          '( %s -> ( 2 ^ T ) e. RR )' % B)
c1 = w.s([tr, t2r, lr, tlt, lb2], 'ltletrd', '( %s -> T < %s )' % (B, LS))
c2 = w.s([tr, lr, l5r, c1, le5b], 'ltletrd', '( %s -> T < ( %s ^ 5 ) )' % (B, LS))
c3 = w.s([xr, tr, l5r, xt, c2], 'lelttrd', '( %s -> X < ( %s ^ 5 ) )' % (B, LS))
w.qed([c3, w.s([xv], 'eqcomd', '( %s -> ( %s ^ 5 ) = %s )' % (B, LS, XCS))], 'breqtrd', '( %s -> X < %s )' % (B, XCS))
run(w)

# ------------------------------------------------------------------ s3filt
DIV = '{ m e. ( 1 ... %s ) | m || %s }' % (LS, LS)
Q21 = '( ; 2 1 / ; ; 1 0 0 )'; Q2120 = '( ; 2 1 / ; 2 0 )'
w = W('s3filt', 'Every divisor of L is at most x ^ ( 21 / 100 ) , so the pigeonhole filter keeps all of them (Lean: Step3W.lean hfilter_all).')
B = 'S e. %s' % FP
sfp = w.s([], 'id', '( %s -> S e. %s )' % (B, FP))
sfi = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B)], 'simprd', '( %s -> S e. Fin )' % B)
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B)], 'simpld', '( %s -> S C_ Prime )' % B)
pn0 = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % B)], 'sstrd', '( %s -> S C_ NN0 )' % B)
sfn0 = w.s([w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % B), w.inst('elfpw')], 'sylibr',
           '( %s -> S e. ( ~P NN0 i^i Fin ) )' % B)
xv = w.s([sfn0, w.inst('xceilval')], 'syl', '( %s -> %s = ( %s ^ 5 ) )' % (B, XCS, LS))
lnn = w.s([sfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (B, LS))
lrp = w.s([lnn], 'nnrpd', '( %s -> %s e. RR+ )' % (B, LS))
lr = w.s([lnn], 'nnred', '( %s -> %s e. RR )' % (B, LS))
l1 = w.s([lnn], 'nnge1d', '( %s -> 1 <_ %s )' % (B, LS))
lge0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % B), w.s([], '1red', '( %s -> 1 e. RR )' % B), lr,
            w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % B), l1], 'letrd', '( %s -> 0 <_ %s )' % (B, LS))
# x ^c ( 21 / 100 ) = L ^c ( 21 / 20 )
q21r = w.s([num.fact(w, Q21, 'RR')], 'a1i', '( %s -> %s e. RR )' % (B, Q21))
q21c = w.s([q21r], 'recnd', '( %s -> %s e. CC )' % (B, Q21))
q2120 = w.s([num.fact(w, Q2120, 'RR')], 'a1i', '( %s -> %s e. RR )' % (B, Q2120))
r5 = w.s([num.fact(w, '5', 'RR')], 'a1i', '( %s -> 5 e. RR )' % B)
cm = w.s([lrp, r5, q21c, w.inst('cxpmul')], 'syl3anc', '( %s -> ( %s ^c ( 5 x. %s ) ) = ( ( %s ^c 5 ) ^c %s ) )' % (B, LS, Q21, LS, Q21))
ce = w.s([w.s([lr], 'recnd', '( %s -> %s e. CC )' % (B, LS)), w.s([num.fact(w, '5', 'NN0')], 'a1i', '( %s -> 5 e. NN0 )' % B),
          w.inst('cxpexp')], 'syl2anc', '( %s -> ( %s ^c 5 ) = ( %s ^ 5 ) )' % (B, LS, LS))
q5 = w.s([w.s([], 'q521100', '( 5 x. %s ) = %s' % (Q21, Q2120))], 'a1i', '( %s -> ( 5 x. %s ) = %s )' % (B, Q21, Q2120))
lhs = w.s([w.s([q5], 'oveq2d', '( %s -> ( %s ^c ( 5 x. %s ) ) = ( %s ^c %s ) )' % (B, LS, Q21, LS, Q2120))], 'eqcomd',
          '( %s -> ( %s ^c %s ) = ( %s ^c ( 5 x. %s ) ) )' % (B, LS, Q2120, LS, Q21))
rhs = w.s([cm, w.s([ce], 'oveq1d', '( %s -> ( ( %s ^c 5 ) ^c %s ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, LS, Q21, LS, Q21))], 'eqtrd',
          '( %s -> ( %s ^c ( 5 x. %s ) ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, LS, Q21, LS, Q21))
xeq = w.s([w.s([xv], 'oveq1d', '( %s -> ( %s ^c %s ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, XCS, Q21, LS, Q21))], 'eqcomd',
          '( %s -> ( ( %s ^ 5 ) ^c %s ) = ( %s ^c %s ) )' % (B, LS, Q21, XCS, Q21))
tot = w.s([w.s([lhs, rhs], 'eqtrd', '( %s -> ( %s ^c %s ) = ( ( %s ^ 5 ) ^c %s ) )' % (B, LS, Q2120, LS, Q21)), xeq], 'eqtrd',
          '( %s -> ( %s ^c %s ) = ( %s ^c %s ) )' % (B, LS, Q2120, XCS, Q21))
one = w.s([], '1red', '( %s -> 1 e. RR )' % B)
le1 = linarith(w, B, [], '1 <_ %s' % Q2120, leaves={})
cx = w.s([lr, l1, one, q2120, le1], 'cxplead', '( %s -> ( %s ^c 1 ) <_ ( %s ^c %s ) )' % (B, LS, LS, Q2120))
c1e = w.s([w.s([lr], 'recnd', '( %s -> %s e. CC )' % (B, LS))], 'cxp1d', '( %s -> ( %s ^c 1 ) = %s )' % (B, LS, LS))
lle = w.s([w.s([c1e], 'eqcomd', '( %s -> %s = ( %s ^c 1 ) )' % (B, LS, LS)), cx], 'eqbrtrd', '( %s -> %s <_ ( %s ^c %s ) )' % (B, LS, LS, Q2120))
lle2 = w.s([lle, tot], 'breqtrd', '( %s -> %s <_ ( %s ^c %s ) )' % (B, LS, XCS, Q21))
xcre = w.s([w.s([tot], 'eqcomd', '( %s -> ( %s ^c %s ) = ( %s ^c %s ) )' % (B, XCS, Q21, LS, Q2120)),
            w.s([lr, lge0, q2120], 'recxpcld', '( %s -> ( %s ^c %s ) e. RR )' % (B, LS, Q2120))], 'eqeltrd',
           '( %s -> ( %s ^c %s ) e. RR )' % (B, XCS, Q21))
# every d in DIV is at most L
C = '( %s /\\ d e. %s )' % (B, DIV)
idm = w.s([], 'id', '( m = d -> m = d )')
cg, _b = w.wcongr('m || %s' % LS, {'m': 'd'}, 'm = d', {'m': idm})
el = w.s([cg], 'elrab', '( d e. %s <-> ( d e. ( 1 ... %s ) /\\ d || %s ) )' % (DIV, LS, LS))
dd = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (C, DIV)),
          w.s([el], 'a1i', '( %s -> ( d e. %s <-> ( d e. ( 1 ... %s ) /\\ d || %s ) ) )' % (C, DIV, LS, LS))], 'mpbid',
         '( %s -> ( d e. ( 1 ... %s ) /\\ d || %s ) )' % (C, LS, LS))
dfz = w.s([dd], 'simpld', '( %s -> d e. ( 1 ... %s ) )' % (C, LS))
dle = w.s([dfz, w.inst('elfzle2')], 'syl', '( %s -> d <_ %s )' % (C, LS))
dnn = w.s([dfz, w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % C)
dre = w.s([dnn], 'nnred', '( %s -> d e. RR )' % C)
fin = w.s([dre, w.s([lr], 'adantr', '( %s -> %s e. RR )' % (C, LS)),
           w.s([xcre], 'adantr', '( %s -> ( %s ^c %s ) e. RR )' % (C, XCS, Q21)),
           dle, w.s([lle2], 'adantr', '( %s -> %s <_ ( %s ^c %s ) )' % (C, LS, XCS, Q21))], 'letrd',
          '( %s -> d <_ ( %s ^c %s ) )' % (C, XCS, Q21))
ral = w.s([fin], 'ralrimiva', '( %s -> A. d e. %s d <_ ( %s ^c %s ) )' % (B, DIV, XCS, Q21))
ri = w.s([ral, w.inst('rabid2im')], 'syl', '( %s -> %s = { d e. %s | d <_ ( %s ^c %s ) } )' % (B, DIV, DIV, XCS, Q21))
w.qed([ri], 'eqcomd', '( %s -> { d e. %s | d <_ ( %s ^c %s ) } = %s )' % (B, DIV, XCS, Q21, DIV))
run(w)

# ------------------------------------------------------------------- s3sum
w = W('s3sum', 'The reciprocal sum over the prime divisors of L is the reciprocal sum over Q.')
B = '( S e. %s /\\ sum_ q e. S ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) )' % FP
sfp = w.s([], 'simpl', '( %s -> S e. %s )' % (B, FP))
hs = w.s([], 'simpr', '( %s -> sum_ q e. S ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) )' % B)
ps = w.s([sfp, w.inst('prmprodset')], 'syl', '( %s -> %s = S )' % (B, PRD))
se = w.s([ps], 'sumeq1d', '( %s -> sum_ q e. %s ( 1 / q ) = sum_ q e. S ( 1 / q ) )' % (B, PRD))
w.qed([se, hs], 'eqbrtrd', '( %s -> sum_ q e. %s ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) )' % (B, PRD))
run(w)

# ------------------------------------------------------------------- s3main
C0 = '( 2 ^c ( -u D - 2 ) )'
E65 = '( exp ` ( ( 6 / 5 ) x. A ) )'
E310 = '( exp ` ( ( 3 / ; 1 0 ) x. A ) )'
E32 = '( exp ` ( ( 3 / 2 ) x. A ) )'
AB = '( A x. B )'
P75 = '( ; 7 5 x. %s )' % AB
ABS1 = '( ( abs ` G ) + 1 )'
KB = '( ( ; 7 5 x. %s ) / %s )' % (ABS1, C0)
SQA = '( A ^ 2 )'

w = WH('s3main', 'The key inequality of Step 3 at windowed scales (Lean: Step3W.lean hmain).')
dr = w.h('D e. RR'); sr = w.h('G e. RR')
ar = w.h('A e. RR'); br = w.h('B e. RR')
a50 = w.h('; 5 0 <_ A'); b0 = w.h('0 < B'); bla = w.h('B <_ A')
tn0 = w.h('T e. NN0'); t3 = w.h('( 3 x. A ) <_ T')
zn0 = w.h('Z e. NN0')
vr = w.h('V e. RR'); v0 = w.h('0 < V'); vle = w.h('V <_ %s' % P75)
zp1 = w.h('( Z + 1 ) <_ %s' % E310)
kr = w.h('K e. RR'); kb = w.h('%s <_ K' % KB); kq = w.h('( K x. %s ) <_ %s' % (SQA, E310))
B_ = 'ph'
LVB = {'A': ar, 'B': br, 'G': sr, 'T': None, 'V': vr}
a0 = linarith(w, B_, [a50], '0 < A', leaves={'A': ar})
ag0 = w.s([a0], 'ltled', '( %s -> 0 <_ A )' % B_)
arp = w.s([ar, a0], 'elrpd', '( %s -> A e. RR+ )' % B_)
brp = w.s([br, b0], 'elrpd', '( %s -> B e. RR+ )' % B_)
abrp = w.s([arp, brp], 'rpmulcld', '( %s -> %s e. RR+ )' % (B_, AB))
abr = w.s([abrp], 'rpred', '( %s -> %s e. RR )' % (B_, AB))
r75 = w.s([num.fact(w, '; 7 5', 'RR+')], 'a1i', '( %s -> ; 7 5 e. RR+ )' % B_)
p75rp = w.s([r75, abrp], 'rpmulcld', '( %s -> %s e. RR+ )' % (B_, P75))
p75r = w.s([p75rp], 'rpred', '( %s -> %s e. RR )' % (B_, P75))
p750 = w.s([p75rp], 'rpgt0d', '( %s -> 0 < %s )' % (B_, P75))
vrp = w.s([vr, v0], 'elrpd', '( %s -> V e. RR+ )' % B_)
# C0 e. RR+
d2r = w.s([w.s([dr], 'renegd' if False else 'renegcld', '( %s -> -u D e. RR )' % B_), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % B_)], 'resubcld', '( %s -> ( -u D - 2 ) e. RR )' % B_)
c0rp = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % B_), d2r], 'rpcxpcld', '( %s -> %s e. RR+ )' % (B_, C0))
c0r = w.s([c0rp], 'rpred', '( %s -> %s e. RR )' % (B_, C0))
c0g0 = w.s([c0rp], 'rpge0d', '( %s -> 0 <_ %s )' % (B_, C0))
c0gt = w.s([c0rp], 'rpgt0d', '( %s -> 0 < %s )' % (B_, C0))
# ( C0 / P75 ) <_ ( C0 / V )
ld = w.s([w.s([vr, v0], 'jca', '( %s -> ( V e. RR /\\ 0 < V ) )' % B_),
          w.s([p75r, p750], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (B_, P75, P75)),
          w.s([c0r, c0gt], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (B_, C0, C0)), w.inst('lediv2')], 'syl3anc',
         '( %s -> ( V <_ %s <-> ( %s / %s ) <_ ( %s / V ) ) )' % (B_, P75, C0, P75, C0))
dv = w.s([vle, ld], 'mpbid', '( %s -> ( %s / %s ) <_ ( %s / V ) )' % (B_, C0, P75, C0))
cp = w.s([c0rp, p75rp], 'rpdivcld', '( %s -> ( %s / %s ) e. RR+ )' % (B_, C0, P75))
cpr = w.s([cp], 'rpred', '( %s -> ( %s / %s ) e. RR )' % (B_, C0, P75))
cp0 = w.s([cp], 'rpge0d', '( %s -> 0 <_ ( %s / %s ) )' % (B_, C0, P75))
cvr = w.s([c0rp, vrp], 'rpdivcld', '( %s -> ( %s / V ) e. RR+ )' % (B_, C0))
cvrr = w.s([cvr], 'rpred', '( %s -> ( %s / V ) e. RR )' % (B_, C0))
# E32 <_ 2 ^ T
tw = w.s([tn0, ar, ag0, t3], 's3twot', '( %s -> %s <_ ( 2 ^ T ) )' % (B_, E32))
h32 = w.s([num.fact(w, '( 3 / 2 )', 'RR')], 'a1i', '( %s -> ( 3 / 2 ) e. RR )' % B_)
h310 = w.s([num.fact(w, '( 3 / ; 1 0 )', 'RR')], 'a1i', '( %s -> ( 3 / ; 1 0 ) e. RR )' % B_)
h65 = w.s([num.fact(w, '( 6 / 5 )', 'RR')], 'a1i', '( %s -> ( 6 / 5 ) e. RR )' % B_)
e32r = w.s([w.s([h32, ar], 'remulcld', '( %s -> ( ( 3 / 2 ) x. A ) e. RR )' % B_)], 'reefcld', '( %s -> %s e. RR )' % (B_, E32))
e310r = w.s([w.s([h310, ar], 'remulcld', '( %s -> ( ( 3 / ; 1 0 ) x. A ) e. RR )' % B_)], 'reefcld', '( %s -> %s e. RR )' % (B_, E310))
e65r = w.s([w.s([h65, ar], 'remulcld', '( %s -> ( ( 6 / 5 ) x. A ) e. RR )' % B_)], 'reefcld', '( %s -> %s e. RR )' % (B_, E65))
e32g = w.s([w.s([h32, ar], 'remulcld', '( %s -> ( ( 3 / 2 ) x. A ) e. RR )' % B_), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (B_, E32))
e32g0 = w.s([e32g], 'ltled', '( %s -> 0 <_ %s )' % (B_, E32))
e65g = w.s([w.s([h65, ar], 'remulcld', '( %s -> ( ( 6 / 5 ) x. A ) e. RR )' % B_), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (B_, E65))
e65g0 = w.s([e65g], 'ltled', '( %s -> 0 <_ %s )' % (B_, E65))
t2r = w.s([w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % B_), tn0], 'nnexpcld', '( %s -> ( 2 ^ T ) e. NN )' % B_)], 'nnred',
          '( %s -> ( 2 ^ T ) e. RR )' % B_)
m6 = w.s([cpr, cvrr, e32r, t2r, cp0, e32g0, dv, tw], 'lemul12ad',
         '( %s -> ( ( %s / %s ) x. %s ) <_ ( ( %s / V ) x. ( 2 ^ T ) ) )' % (B_, C0, P75, E32, C0))
# E32 = E310 x. E65
qq = w.s([w.s([], 'q31065', '( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) = ( 3 / 2 )')], 'a1i', '( %s -> ( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) = ( 3 / 2 ) )' % B_)
h310c = w.s([h310], 'recnd', '( %s -> ( 3 / ; 1 0 ) e. CC )' % B_)
h65c = w.s([h65], 'recnd', '( %s -> ( 6 / 5 ) e. CC )' % B_)
arc = w.s([ar], 'recnd', '( %s -> A e. CC )' % B_)
ad = w.s([h310c, h65c, arc], 'adddird', '( %s -> ( ( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) x. A ) = ( ( ( 3 / ; 1 0 ) x. A ) + ( ( 6 / 5 ) x. A ) ) )' % B_)
ad2 = w.s([w.s([w.s([qq], 'oveq1d', '( %s -> ( ( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) x. A ) = ( ( 3 / 2 ) x. A ) )' % B_)], 'eqcomd',
               '( %s -> ( ( 3 / 2 ) x. A ) = ( ( ( 3 / ; 1 0 ) + ( 6 / 5 ) ) x. A ) )' % B_), ad], 'eqtrd',
          '( %s -> ( ( 3 / 2 ) x. A ) = ( ( ( 3 / ; 1 0 ) x. A ) + ( ( 6 / 5 ) x. A ) ) )' % B_)
efa = w.s([w.s([w.s([h310, ar], 'remulcld', '( %s -> ( ( 3 / ; 1 0 ) x. A ) e. RR )' % B_)], 'recnd', '( %s -> ( ( 3 / ; 1 0 ) x. A ) e. CC )' % B_),
           w.s([w.s([h65, ar], 'remulcld', '( %s -> ( ( 6 / 5 ) x. A ) e. RR )' % B_)], 'recnd', '( %s -> ( ( 6 / 5 ) x. A ) e. CC )' % B_),
           w.inst('efadd')], 'syl2anc',
          '( %s -> ( exp ` ( ( ( 3 / ; 1 0 ) x. A ) + ( ( 6 / 5 ) x. A ) ) ) = ( %s x. %s ) )' % (B_, E310, E65))
e32e = w.s([w.s([ad2], 'fveq2d', '( %s -> %s = ( exp ` ( ( ( 3 / ; 1 0 ) x. A ) + ( ( 6 / 5 ) x. A ) ) ) )' % (B_, E32)), efa], 'eqtrd',
           '( %s -> %s = ( %s x. %s ) )' % (B_, E32, E310, E65))
# ABS1 <_ ( ( C0 / P75 ) x. E310 )
absr = w.s([w.s([sr], 'recnd', '( %s -> G e. CC )' % B_)], 'abscld', '( %s -> ( abs ` G ) e. RR )' % B_)
absg = w.s([w.s([sr], 'recnd', '( %s -> G e. CC )' % B_)], 'absge0d', '( %s -> 0 <_ ( abs ` G ) )' % B_)
sles = w.s([sr], 'leabsd', '( %s -> G <_ ( abs ` G ) )' % B_)
abs1r = w.s([absr, w.s([], '1red', '( %s -> 1 e. RR )' % B_)], 'readdcld', '( %s -> %s e. RR )' % (B_, ABS1))
abs10 = linarith(w, B_, [absg], '0 <_ %s' % ABS1, leaves={'( abs ` G )': absr})
n75r = w.s([num.fact(w, '; 7 5', 'RR')], 'a1i', '( %s -> ; 7 5 e. RR )' % B_)
p7ar = w.s([n75r, abs1r], 'remulcld', '( %s -> ( ; 7 5 x. %s ) e. RR )' % (B_, ABS1))
p7a0 = linarith(w, B_, [absg], '0 <_ ( ; 7 5 x. %s )' % ABS1, leaves={'( abs ` G )': absr})
kbr = w.s([p7ar, c0rp], 'rerpdivcld', '( %s -> %s e. RR )' % (B_, KB))
kb0 = w.s([p7ar, c0rp, p7a0], 'divge0d', '( %s -> 0 <_ %s )' % (B_, KB))
sqr = w.s([ar], 'resqcld', '( %s -> %s e. RR )' % (B_, SQA))
sq0 = w.s([ar], 'sqge0d', '( %s -> 0 <_ %s )' % (B_, SQA))
m8a = w.s([kbr, kr, sqr, sq0, kb], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( K x. %s ) )' % (B_, KB, SQA, SQA))
kbs = w.s([kbr, sqr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (B_, KB, SQA))
ksq = w.s([kr, sqr], 'remulcld', '( %s -> ( K x. %s ) e. RR )' % (B_, SQA))
m8b = w.s([kbs, ksq, e310r, m8a, kq], 'letrd', '( %s -> ( %s x. %s ) <_ %s )' % (B_, KB, SQA, E310))
mba = w.s([br, ar, ar, ag0, bla], 'lemul2ad', '( %s -> %s <_ ( A x. A ) )' % (B_, AB))
sva = w.s([w.s([ar], 'recnd', '( %s -> A e. CC )' % B_)], 'sqvald', '( %s -> %s = ( A x. A ) )' % (B_, SQA))
mba2 = w.s([mba, w.s([sva], 'eqcomd', '( %s -> ( A x. A ) = %s )' % (B_, SQA))], 'breqtrd', '( %s -> %s <_ %s )' % (B_, AB, SQA))
m8c = w.s([abr, sqr, kbr, kb0, mba2], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (B_, KB, AB, KB, SQA))
kab = w.s([kbr, abr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (B_, KB, AB))
m8d = w.s([kab, kbs, e310r, m8c, m8b], 'letrd', '( %s -> ( %s x. %s ) <_ %s )' % (B_, KB, AB, E310))
m8e = w.s([kab, e310r, c0r, c0g0, m8d], 'lemul1ad', '( %s -> ( ( %s x. %s ) x. %s ) <_ ( %s x. %s ) )' % (B_, KB, AB, C0, E310, C0))
kbc = w.s([kbr], 'recnd', '( %s -> %s e. CC )' % (B_, KB))
abc = w.s([abr], 'recnd', '( %s -> %s e. CC )' % (B_, AB))
c0c = w.s([c0r], 'recnd', '( %s -> %s e. CC )' % (B_, C0))
m32 = w.s([kbc, abc, c0c], 'mul32d', '( %s -> ( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s ) )' % (B_, KB, AB, C0, KB, C0, AB))
dc1 = w.s([w.s([p7ar], 'recnd', '( %s -> ( ; 7 5 x. %s ) e. CC )' % (B_, ABS1)), c0c, w.s([c0rp], 'rpne0d', '( %s -> %s =/= 0 )' % (B_, C0))], 'divcan1d',
          '( %s -> ( %s x. %s ) = ( ; 7 5 x. %s ) )' % (B_, KB, C0, ABS1))
m32b = w.s([m32, w.s([dc1], 'oveq1d', '( %s -> ( ( %s x. %s ) x. %s ) = ( ( ; 7 5 x. %s ) x. %s ) )' % (B_, KB, C0, AB, ABS1, AB))], 'eqtrd',
           '( %s -> ( ( %s x. %s ) x. %s ) = ( ( ; 7 5 x. %s ) x. %s ) )' % (B_, KB, AB, C0, ABS1, AB))
n75c = w.s([n75r], 'recnd', '( %s -> ; 7 5 e. CC )' % B_)
abs1c = w.s([abs1r], 'recnd', '( %s -> %s e. CC )' % (B_, ABS1))
g1 = w.s([n75c, abs1c, abc], 'mulassd', '( %s -> ( ( ; 7 5 x. %s ) x. %s ) = ( ; 7 5 x. ( %s x. %s ) ) )' % (B_, ABS1, AB, ABS1, AB))
g2 = w.s([n75c, abs1c, abc], 'mul12d', '( %s -> ( ; 7 5 x. ( %s x. %s ) ) = ( %s x. %s ) )' % (B_, ABS1, AB, ABS1, P75))
g3 = w.s([g1, g2], 'eqtrd', '( %s -> ( ( ; 7 5 x. %s ) x. %s ) = ( %s x. %s ) )' % (B_, ABS1, AB, ABS1, P75))
mc = w.s([e310r, c0r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (B_, E310, C0))
cm310 = w.s([w.s([e310r], 'recnd', '( %s -> %s e. CC )' % (B_, E310)), c0c], 'mulcomd',
            '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (B_, E310, C0, C0, E310))
m8f = w.s([w.s([w.s([m32b, g3], 'eqtrd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. %s ) )' % (B_, KB, AB, C0, ABS1, P75))], 'eqcomd',
               '( %s -> ( %s x. %s ) = ( ( %s x. %s ) x. %s ) )' % (B_, ABS1, P75, KB, AB, C0)), m8e], 'eqbrtrd',
          '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (B_, ABS1, P75, E310, C0))
m8g = w.s([m8f, cm310], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (B_, ABS1, P75, C0, E310))
c0e = w.s([c0r, e310r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (B_, C0, E310))
bi2 = w.s([abs1r, c0e, w.s([p75r, p750], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (B_, P75, P75)), w.inst('lemuldiv')], 'syl3anc',
          '( %s -> ( ( %s x. %s ) <_ ( %s x. %s ) <-> %s <_ ( ( %s x. %s ) / %s ) ) )' % (B_, ABS1, P75, C0, E310, ABS1, C0, E310, P75))
m8h = w.s([m8g, bi2], 'mpbid', '( %s -> %s <_ ( ( %s x. %s ) / %s ) )' % (B_, ABS1, C0, E310, P75))
d23 = w.s([c0c, w.s([e310r], 'recnd', '( %s -> %s e. CC )' % (B_, E310)), w.s([p75r], 'recnd', '( %s -> %s e. CC )' % (B_, P75)),
           w.s([p75rp], 'rpne0d', '( %s -> %s =/= 0 )' % (B_, P75))], 'div23d',
          '( %s -> ( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s ) )' % (B_, C0, E310, P75, C0, P75, E310))
m8 = w.s([m8h, d23], 'breqtrd', '( %s -> %s <_ ( ( %s / %s ) x. %s ) )' % (B_, ABS1, C0, P75, E310))
# ( Z + 1 ) <_ E65
lx = linarith(w, B_, [ag0], '( ( 3 / ; 1 0 ) x. A ) <_ ( ( 6 / 5 ) x. A )', leaves={'A': ar})
bie = w.s([w.s([h310, ar], 'remulcld', '( %s -> ( ( 3 / ; 1 0 ) x. A ) e. RR )' % B_),
           w.s([h65, ar], 'remulcld', '( %s -> ( ( 6 / 5 ) x. A ) e. RR )' % B_), w.inst('efle')], 'syl2anc',
          '( %s -> ( ( ( 3 / ; 1 0 ) x. A ) <_ ( ( 6 / 5 ) x. A ) <-> %s <_ %s ) )' % (B_, E310, E65))
e36 = w.s([lx, bie], 'mpbid', '( %s -> %s <_ %s )' % (B_, E310, E65))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % B_)
zp1r = w.s([zr, w.s([], '1red', '( %s -> 1 e. RR )' % B_)], 'readdcld', '( %s -> ( Z + 1 ) e. RR )' % B_)
z65 = w.s([zp1r, e310r, e65r, zp1, e36], 'letrd', '( %s -> ( Z + 1 ) <_ %s )' % (B_, E65))
# assemble
se = w.s([sr, absr, e65r, e65g0, sles], 'lemul1ad', '( %s -> ( G x. %s ) <_ ( ( abs ` G ) x. %s ) )' % (B_, E65, E65))
absc = w.s([absr], 'recnd', '( %s -> ( abs ` G ) e. CC )' % B_)
adr = w.s([absc, w.s([], '1cnd', '( %s -> 1 e. CC )' % B_), w.s([e65r], 'recnd', '( %s -> %s e. CC )' % (B_, E65))], 'adddird',
          '( %s -> ( %s x. %s ) = ( ( ( abs ` G ) x. %s ) + ( 1 x. %s ) ) )' % (B_, ABS1, E65, E65, E65))
oneE = w.s([w.s([e65r], 'recnd', '( %s -> %s e. CC )' % (B_, E65))], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (B_, E65, E65))
adr2 = w.s([adr, w.s([oneE], 'oveq2d', '( %s -> ( ( ( abs ` G ) x. %s ) + ( 1 x. %s ) ) = ( ( ( abs ` G ) x. %s ) + %s ) )' % (B_, E65, E65, E65, E65))], 'eqtrd',
           '( %s -> ( %s x. %s ) = ( ( ( abs ` G ) x. %s ) + %s ) )' % (B_, ABS1, E65, E65, E65))
sser = w.s([sr, e65r], 'remulcld', '( %s -> ( G x. %s ) e. RR )' % (B_, E65))
aser = w.s([absr, e65r], 'remulcld', '( %s -> ( ( abs ` G ) x. %s ) e. RR )' % (B_, E65))
lin2 = linarith(w, B_, [se, z65], '( ( G x. %s ) + ( Z + 1 ) ) <_ ( ( ( abs ` G ) x. %s ) + %s )' % (E65, E65, E65),
                leaves={'( G x. %s )' % E65: sser, '( ( abs ` G ) x. %s )' % E65: aser, 'Z': zr, E65: e65r})
lin3 = w.s([lin2, w.s([adr2], 'eqcomd', '( %s -> ( ( ( abs ` G ) x. %s ) + %s ) = ( %s x. %s ) )' % (B_, E65, E65, ABS1, E65))], 'breqtrd',
           '( %s -> ( ( G x. %s ) + ( Z + 1 ) ) <_ ( %s x. %s ) )' % (B_, E65, ABS1, E65))
cpe = w.s([cpr, e310r], 'remulcld', '( %s -> ( ( %s / %s ) x. %s ) e. RR )' % (B_, C0, P75, E310))
m13 = w.s([abs1r, cpe, e65r, e65g0, m8], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( ( ( %s / %s ) x. %s ) x. %s ) )' % (B_, ABS1, E65, C0, P75, E310, E65))
ma = w.s([w.s([cpr], 'recnd', '( %s -> ( %s / %s ) e. CC )' % (B_, C0, P75)), w.s([e310r], 'recnd', '( %s -> %s e. CC )' % (B_, E310)),
          w.s([e65r], 'recnd', '( %s -> %s e. CC )' % (B_, E65))], 'mulassd',
         '( %s -> ( ( ( %s / %s ) x. %s ) x. %s ) = ( ( %s / %s ) x. ( %s x. %s ) ) )' % (B_, C0, P75, E310, E65, C0, P75, E310, E65))
mb = w.s([ma, w.s([w.s([e32e], 'eqcomd', '( %s -> ( %s x. %s ) = %s )' % (B_, E310, E65, E32))], 'oveq2d',
                  '( %s -> ( ( %s / %s ) x. ( %s x. %s ) ) = ( ( %s / %s ) x. %s ) )' % (B_, C0, P75, E310, E65, C0, P75, E32))], 'eqtrd',
         '( %s -> ( ( ( %s / %s ) x. %s ) x. %s ) = ( ( %s / %s ) x. %s ) )' % (B_, C0, P75, E310, E65, C0, P75, E32))
m13b = w.s([m13, mb], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( ( %s / %s ) x. %s ) )' % (B_, ABS1, E65, C0, P75, E32))
lhsr = w.s([sser, zp1r], 'readdcld', '( %s -> ( ( G x. %s ) + ( Z + 1 ) ) e. RR )' % (B_, E65))
abser = w.s([abs1r, e65r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (B_, ABS1, E65))
cpe32 = w.s([cpr, e32r], 'remulcld', '( %s -> ( ( %s / %s ) x. %s ) e. RR )' % (B_, C0, P75, E32))
cvt = w.s([cvrr, t2r], 'remulcld', '( %s -> ( ( %s / V ) x. ( 2 ^ T ) ) e. RR )' % (B_, C0))
t1 = w.s([lhsr, abser, cpe32, lin3, m13b], 'letrd', '( %s -> ( ( G x. %s ) + ( Z + 1 ) ) <_ ( ( %s / %s ) x. %s ) )' % (B_, E65, C0, P75, E32))
w.qed([lhsr, cpe32, cvt, t1, m6], 'letrd', '( %s -> ( ( G x. %s ) + ( Z + 1 ) ) <_ ( ( %s / V ) x. ( 2 ^ T ) ) )' % (B_, E65, C0))
run(w)

# --------------------------------------------------------------------- s3lx
w = WH('s3lx', 'L = Lmod Q and x = L ^ 5 are at least 2 .')
sfp = w.h('S e. %s' % FP)
hc = w.h('( # ` S ) = T')
t1 = w.h('1 <_ T')
B_ = 'ph'
sfi = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B_)], 'simprd', '( %s -> S e. Fin )' % B_)
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B_)], 'simpld', '( %s -> S C_ Prime )' % B_)
tn0 = w.s([hc, w.s([sfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % B_)], 'eqeltrrd', '( %s -> T e. NN0 )' % B_)
tz = w.s([tn0], 'nn0zd', '( %s -> T e. ZZ )' % B_)
oz = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % B_)
tuz = w.s([w.s([oz, tz, t1], '3jca', '( %s -> ( 1 e. ZZ /\\ T e. ZZ /\\ 1 <_ T ) )' % B_), w.inst('eluz2')], 'sylibr',
          '( %s -> T e. ( ZZ>= ` 1 ) )' % B_)
r2r = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % B_)
le2 = w.s([w.s([], '1le2', '1 <_ 2')], 'a1i', '( %s -> 1 <_ 2 )' % B_)
ex1 = w.s([r2r, le2, tuz, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ 1 ) <_ ( 2 ^ T ) )' % B_)
e21 = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % B_)
e21b = w.s([e21], 'exp1d', '( %s -> ( 2 ^ 1 ) = 2 )' % B_)
ex2 = w.s([w.s([e21b], 'eqcomd', '( %s -> 2 = ( 2 ^ 1 ) )' % B_), ex1], 'eqbrtrd', '( %s -> 2 <_ ( 2 ^ T ) )' % B_)
lb = w.s([sfp, w.inst('prmprodlb')], 'syl', '( %s -> ( 2 ^ ( # ` S ) ) <_ %s )' % (B_, LS))
lb2 = w.s([w.s([w.s([hc], 'oveq2d', '( %s -> ( 2 ^ ( # ` S ) ) = ( 2 ^ T ) )' % B_)], 'eqcomd',
               '( %s -> ( 2 ^ T ) = ( 2 ^ ( # ` S ) ) )' % B_), lb], 'eqbrtrd', '( %s -> ( 2 ^ T ) <_ %s )' % (B_, LS))
lnn = w.s([sfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (B_, LS))
lr = w.s([lnn], 'nnred', '( %s -> %s e. RR )' % (B_, LS))
l1 = w.s([lnn], 'nnge1d', '( %s -> 1 <_ %s )' % (B_, LS))
t2r = w.s([w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % B_), tn0], 'nnexpcld', '( %s -> ( 2 ^ T ) e. NN )' % B_)], 'nnred',
          '( %s -> ( 2 ^ T ) e. RR )' % B_)
l2 = w.s([r2r, t2r, lr, ex2, lb2], 'letrd', '( %s -> 2 <_ %s )' % (B_, LS))
n5uc = w.s([w.s([], '5nn', '5 e. NN'), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtri', '5 e. ( ZZ>= ` 1 )')
n5u = w.s([n5uc], 'a1i', '( %s -> 5 e. ( ZZ>= ` 1 ) )' % B_)
le5 = w.s([lr, l1, n5u, w.inst('leexp2a')], 'syl3anc', '( %s -> ( %s ^ 1 ) <_ ( %s ^ 5 ) )' % (B_, LS, LS))
e1 = w.s([w.s([lr], 'recnd', '( %s -> %s e. CC )' % (B_, LS))], 'exp1d', '( %s -> ( %s ^ 1 ) = %s )' % (B_, LS, LS))
le5b = w.s([w.s([e1], 'eqcomd', '( %s -> %s = ( %s ^ 1 ) )' % (B_, LS, LS)), le5], 'eqbrtrd', '( %s -> %s <_ ( %s ^ 5 ) )' % (B_, LS, LS))
pn0 = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % B_)], 'sstrd', '( %s -> S C_ NN0 )' % B_)
sfn0 = w.s([w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % B_), w.inst('elfpw')], 'sylibr',
           '( %s -> S e. ( ~P NN0 i^i Fin ) )' % B_)
xv = w.s([sfn0, w.inst('xceilval')], 'syl', '( %s -> %s = ( %s ^ 5 ) )' % (B_, XCS, LS))
l5r = w.s([lr, w.s([num.fact(w, '5', 'NN0')], 'a1i', '( %s -> 5 e. NN0 )' % B_)], 'reexpcld', '( %s -> ( %s ^ 5 ) e. RR )' % (B_, LS))
x2 = w.s([r2r, lr, l5r, l2, le5b], 'letrd', '( %s -> 2 <_ ( %s ^ 5 ) )' % (B_, LS))
x2b = w.s([x2, w.s([xv], 'eqcomd', '( %s -> ( %s ^ 5 ) = %s )' % (B_, LS, XCS))], 'breqtrd', '( %s -> 2 <_ %s )' % (B_, XCS))
w.qed([l2, x2b], 'jca', '( %s -> ( 2 <_ %s /\\ 2 <_ %s ) )' % (B_, LS, XCS))
run(w)

# ------------------------------------------------------------------- s3pool
DIVS = '{ m e. ( 1 ... %s ) | m || %s }' % (LS, LS)
FILT = '{ d e. %s | d <_ ( %s ^c %s ) }' % (DIVS, XCS, Q21)
R3 = '{ d e. %s | ( ( ( d x. K ) + 1 ) <_ %s /\\ ( ( d x. K ) + 1 ) e. Prime /\\ Z < ( ( d x. K ) + 1 ) ) }' % (DIVS, XCS)
R2 = '{ d e. %s | ( ( ( d x. K ) + 1 ) <_ %s /\\ ( ( d x. K ) + 1 ) e. Prime ) }' % (DIVS, XCS)
CQ = '( ( 2 ^c ( -u D - 2 ) ) / ( log ` %s ) )' % XCS
POOLS = '( ( S pool Z ) ` K )'

w = WH('s3pool', 'The pigeonhole count transferred to the pool (Lean: Step3W.lean hcount with hfilter_all, hdivcard, hcard_split).')
sfp = w.h('S e. %s' % FP)
hc = w.h('( # ` S ) = T')
zn0 = w.h('Z e. NN0'); knn = w.h('K e. NN')
dr = w.h('D e. RR')
lx0 = w.h('0 < ( log ` %s )' % XCS)
hp = w.h('( %s x. ( # ` %s ) ) <_ ( # ` %s )' % (CQ, FILT, R2))
B_ = 'ph'
sfi = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B_)], 'simprd', '( %s -> S e. Fin )' % B_)
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % B_)], 'simpld', '( %s -> S C_ Prime )' % B_)
pn0 = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % B_)], 'sstrd', '( %s -> S C_ NN0 )' % B_)
sfn0 = w.s([w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % B_), w.inst('elfpw')], 'sylibr',
           '( %s -> S e. ( ~P NN0 i^i Fin ) )' % B_)
ft = w.s([sfp, w.inst('s3filt')], 'syl', '( %s -> %s = %s )' % (B_, FILT, DIVS))
dc = w.s([sfp, w.inst('prmproddivcard')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` S ) ) )' % (B_, DIVS))
dc2 = w.s([dc, w.s([hc], 'oveq2d', '( %s -> ( 2 ^ ( # ` S ) ) = ( 2 ^ T ) )' % B_)], 'eqtrd',
          '( %s -> ( # ` %s ) = ( 2 ^ T ) )' % (B_, DIVS))
fc = w.s([w.s([ft], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (B_, FILT, DIVS)), dc2], 'eqtrd',
         '( %s -> ( # ` %s ) = ( 2 ^ T ) )' % (B_, FILT))
hp2 = w.s([w.s([w.s([fc], 'oveq2d', '( %s -> ( %s x. ( # ` %s ) ) = ( %s x. ( 2 ^ T ) ) )' % (B_, CQ, FILT, CQ))], 'eqcomd',
               '( %s -> ( %s x. ( 2 ^ T ) ) = ( %s x. ( # ` %s ) ) )' % (B_, CQ, CQ, FILT)), hp], 'eqbrtrd',
          '( %s -> ( %s x. ( 2 ^ T ) ) <_ ( # ` %s ) )' % (B_, CQ, R2))
j3 = w.s([sfn0, zn0, knn], '3jca', '( %s -> ( S e. ( ~P NN0 i^i Fin ) /\\ Z e. NN0 /\\ K e. NN ) )' % B_)
pc = w.s([j3, w.inst('poolcard')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (B_, R3, POOLS))
pc2 = w.s([j3, w.inst('poolcard2')], 'syl', '( %s -> ( # ` %s ) <_ ( ( # ` %s ) + ( Z + 1 ) ) )' % (B_, R2, R3))
pc3 = w.s([pc2, w.s([pc], 'oveq1d', '( %s -> ( ( # ` %s ) + ( Z + 1 ) ) = ( ( # ` %s ) + ( Z + 1 ) ) )' % (B_, R3, POOLS))], 'breqtrd',
          '( %s -> ( # ` %s ) <_ ( ( # ` %s ) + ( Z + 1 ) ) )' % (B_, R2, POOLS))
divfi = w.s([w.s([], 'fzfi', '( 1 ... %s ) e. Fin' % LS), w.inst('rabfi')], 'ax-mp', '%s e. Fin' % DIVS)
r2fi = w.s([w.s([divfi, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % R2)], 'a1i', '( %s -> %s e. Fin )' % (B_, R2))
h2r = w.s([w.s([r2fi, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (B_, R2))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (B_, R2))
poolfi = w.s([j3, w.inst('poolfi')], 'syl', '( %s -> %s e. Fin )' % (B_, POOLS)) if False else w.s([w.s([sfn0, zn0, w.s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % B_)], '3jca', '( %s -> ( S e. ( ~P NN0 i^i Fin ) /\\ Z e. NN0 /\\ K e. NN0 ) )' % B_), w.inst('poolfi')], 'syl', '( %s -> %s e. Fin )' % (B_, POOLS))
hpr = w.s([w.s([poolfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (B_, POOLS))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (B_, POOLS))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % B_)
sumr = w.s([hpr, w.s([zr, w.s([], '1red', '( %s -> 1 e. RR )' % B_)], 'readdcld', '( %s -> ( Z + 1 ) e. RR )' % B_)], 'readdcld',
           '( %s -> ( ( # ` %s ) + ( Z + 1 ) ) e. RR )' % (B_, POOLS))
lxr = w.s([w.s([w.s([sfp, w.inst('xceilcl')], 'syl', '( %s -> %s e. NN )' % (B_, XCS))], 'nnrpd', '( %s -> %s e. RR+ )' % (B_, XCS)), w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (B_, XCS))
lxrp = w.s([lxr, lx0], 'elrpd', '( %s -> ( log ` %s ) e. RR+ )' % (B_, XCS))
dneg = w.s([w.s([dr], 'renegcld', '( %s -> -u D e. RR )' % B_), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % B_)], 'resubcld', '( %s -> ( -u D - 2 ) e. RR )' % B_)
c0rp = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % B_), dneg], 'rpcxpcld', '( %s -> ( 2 ^c ( -u D - 2 ) ) e. RR+ )' % B_)
cqr = w.s([c0rp, lxrp], 'rpdivcld', '( %s -> %s e. RR+ )' % (B_, CQ))
cqrr = w.s([cqr], 'rpred', '( %s -> %s e. RR )' % (B_, CQ))
t2rr = w.s([w.s([w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % B_), w.s([hc, w.s([sfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % B_)], 'eqeltrrd', '( %s -> T e. NN0 )' % B_)], 'nnexpcld', '( %s -> ( 2 ^ T ) e. NN )' % B_)], 'nnred', '( %s -> ( 2 ^ T ) e. RR )' % B_)
lhsr = w.s([cqrr, t2rr], 'remulcld', '( %s -> ( %s x. ( 2 ^ T ) ) e. RR )' % (B_, CQ))
w.qed([lhsr, h2r, sumr, hp2, pc3], 'letrd', '( %s -> ( %s x. ( 2 ^ T ) ) <_ ( ( # ` %s ) + ( Z + 1 ) ) )' % (B_, CQ, POOLS))
run(w)
