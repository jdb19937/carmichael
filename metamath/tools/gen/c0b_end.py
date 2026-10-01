"""Sortie C0b, batch 9: helpers for the Goursat endgame (abscrle, gourprod)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

# ---- abscrle
w = W('abscrle', 'The absolute value of a complex number is at most the sum of the absolute values of its parts.')
A0 = 'X e. CC'
xc = w.s([], 'id', '( %s -> X e. CC )' % A0)
ic = closed(w, A0, 'ax-icn', '_i e. CC')
xr = w.s([xc, w.inst('recl')], 'syl', '( %s -> ( Re ` X ) e. RR )' % A0)
xi = w.s([xc, w.inst('imcl')], 'syl', '( %s -> ( Im ` X ) e. RR )' % A0)
rc = w.s([xr], 'recnd', '( %s -> ( Re ` X ) e. CC )' % A0)
mc = w.s([xi], 'recnd', '( %s -> ( Im ` X ) e. CC )' % A0)
iim = w.s([ic, mc], 'mulcld', '( %s -> ( _i x. ( Im ` X ) ) e. CC )' % A0)
rep = w.s([xc], 'replimd', '( %s -> X = ( ( Re ` X ) + ( _i x. ( Im ` X ) ) ) )' % A0)
tri = w.s([rc, iim], 'abstrid', '( %s -> ( abs ` ( ( Re ` X ) + ( _i x. ( Im ` X ) ) ) ) <_ ( ( abs ` ( Re ` X ) ) + ( abs ` ( _i x. ( Im ` X ) ) ) )' % A0 + ' )')
absi1 = closed(w, A0, 'absi', '( abs ` _i ) = 1')
am = w.s([w.s([ic, mc], 'absmuld', '( %s -> ( abs ` ( _i x. ( Im ` X ) ) ) = ( ( abs ` _i ) x. ( abs ` ( Im ` X ) ) ) )' % A0),
          w.s([w.s([absi1], 'oveq1d', '( %s -> ( ( abs ` _i ) x. ( abs ` ( Im ` X ) ) ) = ( 1 x. ( abs ` ( Im ` X ) ) ) )' % A0),
               w.s([w.s([mc], 'abscld', '( %s -> ( abs ` ( Im ` X ) ) e. RR )' % A0)], 'recnd', '( %s -> ( abs ` ( Im ` X ) ) e. CC )' % A0)], 'eqtrd' if False else 'eqtrd', 'x')], 'eqtrd', 'y')
w.lines.pop(); w.lines.pop()
one = w.s([w.s([absi1], 'oveq1d', '( %s -> ( ( abs ` _i ) x. ( abs ` ( Im ` X ) ) ) = ( 1 x. ( abs ` ( Im ` X ) ) ) )' % A0),
           w.s([w.s([w.s([mc], 'abscld', '( %s -> ( abs ` ( Im ` X ) ) e. RR )' % A0)], 'recnd', '( %s -> ( abs ` ( Im ` X ) ) e. CC )' % A0)], 'mullidd', '( %s -> ( 1 x. ( abs ` ( Im ` X ) ) ) = ( abs ` ( Im ` X ) ) )' % A0)], 'eqtrd',
          '( %s -> ( ( abs ` _i ) x. ( abs ` ( Im ` X ) ) ) = ( abs ` ( Im ` X ) ) )' % A0)
am = w.s([w.s([ic, mc], 'absmuld', '( %s -> ( abs ` ( _i x. ( Im ` X ) ) ) = ( ( abs ` _i ) x. ( abs ` ( Im ` X ) ) ) )' % A0), one], 'eqtrd',
         '( %s -> ( abs ` ( _i x. ( Im ` X ) ) ) = ( abs ` ( Im ` X ) ) )' % A0)
lhs = w.s([w.s([rep], 'fveq2d', '( %s -> ( abs ` X ) = ( abs ` ( ( Re ` X ) + ( _i x. ( Im ` X ) ) ) ) )' % A0)], 'eqcomd',
          '( %s -> ( abs ` ( ( Re ` X ) + ( _i x. ( Im ` X ) ) ) ) = ( abs ` X ) )' % A0)
w.qed([tri, lhs, w.s([am], 'oveq2d', '( %s -> ( ( abs ` ( Re ` X ) ) + ( abs ` ( _i x. ( Im ` X ) ) ) ) = ( ( abs ` ( Re ` X ) ) + ( abs ` ( Im ` X ) ) ) )' % A0)], '3brtr3d',
      '( %s -> ( abs ` X ) <_ ( ( abs ` ( Re ` X ) ) + ( abs ` ( Im ` X ) ) ) )' % A0); run(w)

# ---- gourprod
w = W('gourprod', 'The product identity behind the Goursat estimate.')
A0 = '( ( P e. CC /\\ P =/= 0 ) /\\ ( X e. CC /\\ E e. CC ) )'
QQ = '( X / P )'
pc = w.s([], 'simpll', '( %s -> P e. CC )' % A0)
pn = w.s([], 'simplr', '( %s -> P =/= 0 )' % A0)
xc = w.s([], 'simprl', '( %s -> X e. CC )' % A0)
ec = w.s([], 'simprr', '( %s -> E e. CC )' % A0)
qc = w.s([xc, pc, pn], 'divcld', '( %s -> %s e. CC )' % (A0, QQ))
t2 = closed(w, A0, '2cn', '2 e. CC')
eq = w.s([ec, qc], 'mulcld', '( %s -> ( E x. %s ) e. CC )' % (A0, QQ))
qq = w.s([qc, qc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A0, QQ, QQ))
pp = w.s([pc, pc], 'mulcld', '( %s -> ( P x. P ) e. CC )' % A0)
s1 = w.s([t2, eq, qc], 'mulassd', '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) = ( 2 x. ( ( E x. %s ) x. %s ) ) )' % (A0, QQ, QQ, QQ, QQ))
s2 = w.s([w.s([ec, qc, qc], 'mulassd', '( %s -> ( ( E x. %s ) x. %s ) = ( E x. ( %s x. %s ) ) )' % (A0, QQ, QQ, QQ, QQ))], 'oveq2d',
         '( %s -> ( 2 x. ( ( E x. %s ) x. %s ) ) = ( 2 x. ( E x. ( %s x. %s ) ) ) )' % (A0, QQ, QQ, QQ, QQ))
s3 = w.s([s1, s2], 'eqtrd', '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) = ( 2 x. ( E x. ( %s x. %s ) ) ) )' % (A0, QQ, QQ, QQ, QQ))
s4 = w.s([s3], 'oveq2d', '( %s -> ( ( P x. P ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( ( P x. P ) x. ( 2 x. ( E x. ( %s x. %s ) ) ) ) )' % (A0, QQ, QQ, QQ, QQ))
s5 = w.s([pp, t2, w.s([ec, qq], 'mulcld', '( %s -> ( E x. ( %s x. %s ) ) e. CC )' % (A0, QQ, QQ))], 'mul12d',
         '( %s -> ( ( P x. P ) x. ( 2 x. ( E x. ( %s x. %s ) ) ) ) = ( 2 x. ( ( P x. P ) x. ( E x. ( %s x. %s ) ) ) ) )' % (A0, QQ, QQ, QQ, QQ))
s6 = w.s([w.s([pp, ec, qq], 'mul12d', '( %s -> ( ( P x. P ) x. ( E x. ( %s x. %s ) ) ) = ( E x. ( ( P x. P ) x. ( %s x. %s ) ) ) )' % (A0, QQ, QQ, QQ, QQ))], 'oveq2d',
         '( %s -> ( 2 x. ( ( P x. P ) x. ( E x. ( %s x. %s ) ) ) ) = ( 2 x. ( E x. ( ( P x. P ) x. ( %s x. %s ) ) ) ) )' % (A0, QQ, QQ, QQ, QQ))
s7 = w.s([w.s([w.s([pc, pc, qc, qc], 'mul4d', '( %s -> ( ( P x. P ) x. ( %s x. %s ) ) = ( ( P x. %s ) x. ( P x. %s ) ) )' % (A0, QQ, QQ, QQ, QQ)),
               w.s([w.s([xc, pc, pn], 'divcan2d', '( %s -> ( P x. %s ) = X )' % (A0, QQ)), w.s([xc, pc, pn], 'divcan2d', '( %s -> ( P x. %s ) = X )' % (A0, QQ))], 'oveq12d',
                   '( %s -> ( ( P x. %s ) x. ( P x. %s ) ) = ( X x. X ) )' % (A0, QQ, QQ))], 'eqtrd', '( %s -> ( ( P x. P ) x. ( %s x. %s ) ) = ( X x. X ) )' % (A0, QQ, QQ))], 'oveq2d',
         '( %s -> ( E x. ( ( P x. P ) x. ( %s x. %s ) ) ) = ( E x. ( X x. X ) ) )' % (A0, QQ, QQ))
s8 = w.s([s7], 'oveq2d', '( %s -> ( 2 x. ( E x. ( ( P x. P ) x. ( %s x. %s ) ) ) ) = ( 2 x. ( E x. ( X x. X ) ) ) )' % (A0, QQ, QQ))
w.qed([w.s([w.s([s4, s5], 'eqtrd', '( %s -> ( ( P x. P ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( 2 x. ( ( P x. P ) x. ( E x. ( %s x. %s ) ) ) ) )' % (A0, QQ, QQ, QQ, QQ)), s6], 'eqtrd',
               '( %s -> ( ( P x. P ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( 2 x. ( E x. ( ( P x. P ) x. ( %s x. %s ) ) ) ) )' % (A0, QQ, QQ, QQ, QQ)), s8], 'eqtrd',
      '( %s -> ( ( P x. P ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( 2 x. ( E x. ( X x. X ) ) ) )' % (A0, QQ, QQ))
run(w)


# ---- gourpt: the pointwise bound on the remainder over a sub-rectangle
FZ = '( F ` Z )'
AFFZ = '( %s + ( C x. ( z - Z ) ) )' % FZ
AFFV = '( %s + ( C x. ( y - Z ) ) )' % FZ
ODEF = 'O = ( y e. D |-> ( ( F ` y ) - %s ) )' % AFFV
def LOC(t):
    return '( ( abs ` ( %s - Z ) ) < R -> ( abs ` ( ( ( F ` %s ) - %s ) - ( C x. ( %s - Z ) ) ) ) <_ ( E x. ( abs ` ( %s - Z ) ) ) )' % (t, t, FZ, t, t)
LOCAL = 'A. s e. D %s' % LOC('s')
DM = '( ( ( Re ` W ) - ( Re ` U ) ) + ( ( Im ` W ) - ( Im ` U ) ) )'
w = W('gourpt', 'The remainder of the linear approximation is small on a small sub-rectangle.')
hyp(w, '1', 'gourpt.o', ODEF)
B1 = '( F e. ( D -cn-> CC ) /\\ ( C e. CC /\\ Z e. CC ) )'
B2 = '( E e. RR+ /\\ R e. RR+ /\\ %s )' % LOCAL
B3 = '( ( U e. CC /\\ W e. CC ) /\\ ( U crect W ) C_ D /\\ ( Z e. ( U crect W ) /\\ %s < R ) )' % DM
A0 = '( %s /\\ %s /\\ %s )' % (B1, B2, B3)
b1 = w.s([], 'simp1', '( %s -> %s )' % (A0, B1))
fcn = w.s([b1, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
cc = w.s([w.s([b1, w.inst('simpr')], 'syl', '( %s -> ( C e. CC /\\ Z e. CC ) )' % A0), w.inst('simpl')], 'syl', '( %s -> C e. CC )' % A0)
zc = w.s([w.s([b1, w.inst('simpr')], 'syl', '( %s -> ( C e. CC /\\ Z e. CC ) )' % A0), w.inst('simpr')], 'syl', '( %s -> Z e. CC )' % A0)
b2 = w.s([], 'simp2', '( %s -> %s )' % (A0, B2))
erp = w.s([b2, w.inst('simp1')], 'syl', '( %s -> E e. RR+ )' % A0)
rrp = w.s([b2, w.inst('simp2')], 'syl', '( %s -> R e. RR+ )' % A0)
loc = w.s([b2, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, LOCAL))
b3 = w.s([], 'simp3', '( %s -> %s )' % (A0, B3))
uc = w.s([w.s([b3, w.inst('simp1')], 'syl', '( %s -> ( U e. CC /\\ W e. CC ) )' % A0), w.inst('simpl')], 'syl', '( %s -> U e. CC )' % A0)
wc = w.s([w.s([b3, w.inst('simp1')], 'syl', '( %s -> ( U e. CC /\\ W e. CC ) )' % A0), w.inst('simpr')], 'syl', '( %s -> W e. CC )' % A0)
rss = w.s([b3, w.inst('simp2')], 'syl', '( %s -> ( U crect W ) C_ D )' % A0)
zr = w.s([w.s([b3, w.inst('simp3')], 'syl', '( %s -> ( Z e. ( U crect W ) /\\ %s < R ) )' % (A0, DM)), w.inst('simpl')], 'syl', '( %s -> Z e. ( U crect W ) )' % A0)
dmr = w.s([w.s([b3, w.inst('simp3')], 'syl', '( %s -> ( Z e. ( U crect W ) /\\ %s < R ) )' % (A0, DM)), w.inst('simpr')], 'syl', '( %s -> %s < R )' % (A0, DM))
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ur = w.s([uc, w.inst('recl')], 'syl', '( %s -> ( Re ` U ) e. RR )' % A0)
wr = w.s([wc, w.inst('recl')], 'syl', '( %s -> ( Re ` W ) e. RR )' % A0)
ui = w.s([uc, w.inst('imcl')], 'syl', '( %s -> ( Im ` U ) e. RR )' % A0)
wi = w.s([wc, w.inst('imcl')], 'syl', '( %s -> ( Im ` W ) e. RR )' % A0)
dmre = w.s([w.s([wr, ur], 'resubcld', '( %s -> ( ( Re ` W ) - ( Re ` U ) ) e. RR )' % A0), w.s([wi, ui], 'resubcld', '( %s -> ( ( Im ` W ) - ( Im ` U ) ) e. RR )' % A0)], 'readdcld', '( %s -> %s e. RR )' % (A0, DM))
ere = w.s([erp, w.inst('rpre')], 'syl', '( %s -> E e. RR )' % A0)
ege = w.s([erp, w.inst('rpge0')], 'syl', '( %s -> 0 <_ E )' % A0)
elcz = w.s([uc, wc], 'jca', '( %s -> ( U e. CC /\\ W e. CC ) )' % A0)
elcb = w.s([elcz, w.inst('elcrect')], 'syl', '( %s -> ( Z e. ( U crect W ) <-> ( Z e. CC /\\ ( Re ` Z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` Z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) ) )' % A0)
ztt = w.s([zr, elcb], 'mpbid', '( %s -> ( Z e. CC /\\ ( Re ` Z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` Z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) )' % A0)
zre = w.s([ztt, w.inst('simp2')], 'syl', '( %s -> ( Re ` Z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) )' % A0)
zim = w.s([ztt, w.inst('simp3')], 'syl', '( %s -> ( Im ` Z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) )' % A0)
# the point z
AZ = '( %s /\\ z e. ( U crect W ) )' % A0
zz = w.s([], 'simpr', '( %s -> z e. ( U crect W ) )' % AZ)
def dn(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (AZ, f))
ffz = dn(ff, 'F : D --> CC'); ucz = dn(uc, 'U e. CC'); wcz = dn(wc, 'W e. CC')
ccz = dn(cc, 'C e. CC'); zcz = dn(zc, 'Z e. CC'); rssz = dn(rss, '( U crect W ) C_ D')
locz = dn(loc, LOCAL); rrpz = dn(rrp, 'R e. RR+'); dmrz = dn(dmr, '%s < R' % DM)
dmrez = dn(dmre, '%s e. RR' % DM); erez = dn(ere, 'E e. RR'); egez = dn(ege, '0 <_ E')
urz = dn(ur, '( Re ` U ) e. RR'); wrz = dn(wr, '( Re ` W ) e. RR')
uiz = dn(ui, '( Im ` U ) e. RR'); wiz = dn(wi, '( Im ` W ) e. RR')
zrez = dn(zre, '( Re ` Z ) e. ( ( Re ` U ) [,] ( Re ` W ) )')
zimz = dn(zim, '( Im ` Z ) e. ( ( Im ` U ) [,] ( Im ` W ) )')
zd = w.s([rssz, zz], 'sseldd', '( %s -> z e. D )' % AZ)
zcc = w.s([w.s([dn(fcn, 'F e. ( D -cn-> CC )'), w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % AZ), zd], 'sseldd', '( %s -> z e. CC )' % AZ)
elcz2 = w.s([w.s([ucz, wcz], 'jca', '( %s -> ( U e. CC /\\ W e. CC ) )' % AZ), w.inst('elcrect')], 'syl',
            '( %s -> ( z e. ( U crect W ) <-> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) ) )' % AZ)
ztt2 = w.s([zz, elcz2], 'mpbid', '( %s -> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) )' % AZ)
zre2 = w.s([ztt2, w.inst('simp2')], 'syl', '( %s -> ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) )' % AZ)
zim2 = w.s([ztt2, w.inst('simp3')], 'syl', '( %s -> ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) )' % AZ)
# the distance bound
sub = w.s([zcc, zcz], 'subcld', '( %s -> ( z - Z ) e. CC )' % AZ)
ar1 = w.s([w.s([w.s([zcc, zcz, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( z - Z ) ) = ( ( Re ` z ) - ( Re ` Z ) ) )' % AZ)], 'fveq2d',
               '( %s -> ( abs ` ( Re ` ( z - Z ) ) ) = ( abs ` ( ( Re ` z ) - ( Re ` Z ) ) ) )' % AZ),
           w.s([w.s([urz, wrz], 'jca', '( %s -> ( ( Re ` U ) e. RR /\\ ( Re ` W ) e. RR ) )' % AZ), w.s([zre2, zrez], 'jca', '( %s -> ( ( Re ` z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) /\\ ( Re ` Z ) e. ( ( Re ` U ) [,] ( Re ` W ) ) ) )' % AZ), w.inst('iccabssub')], 'syl2anc',
               '( %s -> ( abs ` ( ( Re ` z ) - ( Re ` Z ) ) ) <_ ( ( Re ` W ) - ( Re ` U ) ) )' % AZ)], 'eqbrtrd',
          '( %s -> ( abs ` ( Re ` ( z - Z ) ) ) <_ ( ( Re ` W ) - ( Re ` U ) ) )' % AZ)
ar2 = w.s([w.s([w.s([zcc, zcz, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` ( z - Z ) ) = ( ( Im ` z ) - ( Im ` Z ) ) )' % AZ)], 'fveq2d',
               '( %s -> ( abs ` ( Im ` ( z - Z ) ) ) = ( abs ` ( ( Im ` z ) - ( Im ` Z ) ) ) )' % AZ),
           w.s([w.s([uiz, wiz], 'jca', '( %s -> ( ( Im ` U ) e. RR /\\ ( Im ` W ) e. RR ) )' % AZ), w.s([zim2, zimz], 'jca', '( %s -> ( ( Im ` z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) /\\ ( Im ` Z ) e. ( ( Im ` U ) [,] ( Im ` W ) ) ) )' % AZ), w.inst('iccabssub')], 'syl2anc',
               '( %s -> ( abs ` ( ( Im ` z ) - ( Im ` Z ) ) ) <_ ( ( Im ` W ) - ( Im ` U ) ) )' % AZ)], 'eqbrtrd',
          '( %s -> ( abs ` ( Im ` ( z - Z ) ) ) <_ ( ( Im ` W ) - ( Im ` U ) ) )' % AZ)
sumle = w.s([w.s([w.s([w.s([sub, w.inst('recl')], 'syl', '( %s -> ( Re ` ( z - Z ) ) e. RR )' % AZ)], 'recnd', '( %s -> ( Re ` ( z - Z ) ) e. CC )' % AZ)], 'abscld', '( %s -> ( abs ` ( Re ` ( z - Z ) ) ) e. RR )' % AZ),
             w.s([w.s([w.s([sub, w.inst('imcl')], 'syl', '( %s -> ( Im ` ( z - Z ) ) e. RR )' % AZ)], 'recnd', '( %s -> ( Im ` ( z - Z ) ) e. CC )' % AZ)], 'abscld', '( %s -> ( abs ` ( Im ` ( z - Z ) ) ) e. RR )' % AZ),
             w.s([wrz, urz], 'resubcld', '( %s -> ( ( Re ` W ) - ( Re ` U ) ) e. RR )' % AZ),
             w.s([wiz, uiz], 'resubcld', '( %s -> ( ( Im ` W ) - ( Im ` U ) ) e. RR )' % AZ), ar1, ar2], 'le2addd',
            '( %s -> ( ( abs ` ( Re ` ( z - Z ) ) ) + ( abs ` ( Im ` ( z - Z ) ) ) ) <_ %s )' % (AZ, DM))
absz = w.s([sub], 'abscld', '( %s -> ( abs ` ( z - Z ) ) e. RR )' % AZ)
dist = w.s([absz, w.s([w.s([w.s([w.s([sub, w.inst('recl')], 'syl', '( %s -> ( Re ` ( z - Z ) ) e. RR )' % AZ)], 'recnd', '( %s -> ( Re ` ( z - Z ) ) e. CC )' % AZ)], 'abscld', '( %s -> ( abs ` ( Re ` ( z - Z ) ) ) e. RR )' % AZ),
                       w.s([w.s([w.s([sub, w.inst('imcl')], 'syl', '( %s -> ( Im ` ( z - Z ) ) e. RR )' % AZ)], 'recnd', '( %s -> ( Im ` ( z - Z ) ) e. CC )' % AZ)], 'abscld', '( %s -> ( abs ` ( Im ` ( z - Z ) ) ) e. RR )' % AZ)], 'readdcld',
                      '( %s -> ( ( abs ` ( Re ` ( z - Z ) ) ) + ( abs ` ( Im ` ( z - Z ) ) ) ) e. RR )' % AZ), dmrez,
             w.s([sub, w.inst('abscrle')], 'syl', '( %s -> ( abs ` ( z - Z ) ) <_ ( ( abs ` ( Re ` ( z - Z ) ) ) + ( abs ` ( Im ` ( z - Z ) ) ) ) )' % AZ), sumle], 'letrd',
            '( %s -> ( abs ` ( z - Z ) ) <_ %s )' % (AZ, DM))
ltr = w.s([absz, dmrez, w.s([rrpz, w.inst('rpre')], 'syl', '( %s -> R e. RR )' % AZ), dist, dmrz], 'lelttrd', '( %s -> ( abs ` ( z - Z ) ) < R )' % AZ)
# instantiate the local estimate at z
sb1 = w.s([], 'oveq1', '( s = z -> ( s - Z ) = ( z - Z ) )')
sb2 = w.s([w.s([sb1], 'fveq2d', '( s = z -> ( abs ` ( s - Z ) ) = ( abs ` ( z - Z ) ) )')], 'breq1d', '( s = z -> ( ( abs ` ( s - Z ) ) < R <-> ( abs ` ( z - Z ) ) < R ) )')
sb3 = w.s([w.s([w.s([w.s([], 'fveq2', '( s = z -> ( F ` s ) = ( F ` z ) )')], 'oveq1d', '( s = z -> ( ( F ` s ) - %s ) = ( ( F ` z ) - %s ) )' % (FZ, FZ)),
                w.s([sb1], 'oveq2d', '( s = z -> ( C x. ( s - Z ) ) = ( C x. ( z - Z ) ) )')], 'oveq12d',
               '( s = z -> ( ( ( F ` s ) - %s ) - ( C x. ( s - Z ) ) ) = ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) )' % (FZ, FZ))], 'fveq2d',
          '( s = z -> ( abs ` ( ( ( F ` s ) - %s ) - ( C x. ( s - Z ) ) ) ) = ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) )' % (FZ, FZ))
sb4 = w.s([sb3, w.s([w.s([sb1], 'fveq2d', '( s = z -> ( abs ` ( s - Z ) ) = ( abs ` ( z - Z ) ) )')], 'oveq2d', '( s = z -> ( E x. ( abs ` ( s - Z ) ) ) = ( E x. ( abs ` ( z - Z ) ) ) )')], 'breq12d',
          '( s = z -> ( ( abs ` ( ( ( F ` s ) - %s ) - ( C x. ( s - Z ) ) ) ) <_ ( E x. ( abs ` ( s - Z ) ) ) <-> ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) <_ ( E x. ( abs ` ( z - Z ) ) ) ) )' % (FZ, FZ))
sbb = w.s([sb2, sb4], 'imbi12d', '( s = z -> ( %s <-> %s ) )' % (LOC('s'), LOC('z')))
ins = w.s([sbb, locz, zd], 'rspcdva', '( %s -> %s )' % (AZ, LOC('z')))
est = w.s([ltr, ins], 'mpd', '( %s -> ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) <_ ( E x. ( abs ` ( z - Z ) ) ) )' % (AZ, FZ))
# O's value at z, and the final chain
fz = w.s([ffz, zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % AZ)
fZv = w.s([ffz, w.s([rssz, dn(zr, 'Z e. ( U crect W )')], 'sseldd', '( %s -> Z e. D )' % AZ)], 'ffvelcdmd', '( %s -> %s e. CC )' % (AZ, FZ))
czz = w.s([ccz, sub], 'mulcld', '( %s -> ( C x. ( z - Z ) ) e. CC )' % AZ)
ovv2 = closed(w, AZ, 'ovex', '( ( F ` z ) - %s ) e. _V' % AFFZ)
v1 = w.s([], 'oveq1', '( y = z -> ( y - Z ) = ( z - Z ) )')
v2 = w.s([w.s([v1], 'oveq2d', '( y = z -> ( C x. ( y - Z ) ) = ( C x. ( z - Z ) ) )')], 'oveq2d', '( y = z -> %s = %s )' % (AFFV, AFFZ))
v3 = w.s([w.s([], 'fveq2', '( y = z -> ( F ` y ) = ( F ` z ) )'), v2], 'oveq12d', '( y = z -> ( ( F ` y ) - %s ) = ( ( F ` z ) - %s ) )' % (AFFV, AFFZ))
ovz = w.s([zd, ovv2, w.s([v3, '1'], 'fvmptg', '( ( z e. D /\\ ( ( F ` z ) - %s ) e. _V ) -> ( O ` z ) = ( ( F ` z ) - %s ) )' % (AFFZ, AFFZ))], 'syl2anc',
           '( %s -> ( O ` z ) = ( ( F ` z ) - %s ) )' % (AZ, AFFZ))
sp = w.s([ovz, w.s([w.s([fz, fZv, czz], 'subsub4d', '( %s -> ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) = ( ( F ` z ) - %s ) )' % (AZ, FZ, AFFZ))], 'eqcomd',
                    '( %s -> ( ( F ` z ) - %s ) = ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) )' % (AZ, AFFZ, FZ))], 'eqtrd',
         '( %s -> ( O ` z ) = ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) )' % (AZ, FZ))
mul = w.s([w.s([absz, dmrez, w.s([erez, egez], 'jca', '( %s -> ( E e. RR /\\ 0 <_ E ) )' % AZ)], '3jca', '( %s -> ( ( abs ` ( z - Z ) ) e. RR /\\ %s e. RR /\\ ( E e. RR /\\ 0 <_ E ) )' % (AZ, DM) + ' )'), dist, w.inst('lemul2a')], 'syl2anc',
          '( %s -> ( E x. ( abs ` ( z - Z ) ) ) <_ ( E x. %s ) )' % (AZ, DM))
fin = w.s([w.s([w.s([fz, fZv], 'subcld', '( %s -> ( ( F ` z ) - %s ) e. CC )' % (AZ, FZ)), czz], 'subcld', '( %s -> ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) e. CC )' % (AZ, FZ))], 'abscld',
           '( %s -> ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) e. RR )' % (AZ, FZ))
res = w.s([fin, w.s([erez, absz], 'remulcld', '( %s -> ( E x. ( abs ` ( z - Z ) ) ) e. RR )' % AZ), w.s([erez, dmrez], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (AZ, DM)), est, mul], 'letrd',
          '( %s -> ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) <_ ( E x. %s ) )' % (AZ, FZ, DM))
w.qed([w.s([w.s([sp], 'fveq2d', '( %s -> ( abs ` ( O ` z ) ) = ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) )' % (AZ, FZ)), res], 'eqbrtrd',
            '( %s -> ( abs ` ( O ` z ) ) <_ ( E x. %s ) )' % (AZ, DM))], 'ralrimiva',
      '( %s -> A. z e. ( U crect W ) ( abs ` ( O ` z ) ) <_ ( E x. %s ) )' % (A0, DM))
run(w, True)
