"""Sortie C2 section 3.3a: strip geometry and the elementary bounds for Phragmen-Lindelof."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

STR = '( `\' Re " ( X [,] Y ) )'

# ---- elstr -----------------------------------------------------------------
w = W('elstr', 'Membership in the vertical strip, written as a preimage of the real part.')
refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
w.qed([refn, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ ( Re ` Z ) e. ( X [,] Y ) ) )' % STR); run1(w)

# ---- strcc -----------------------------------------------------------------
w = W('strcc', 'The vertical strip is a set of complex numbers.')
dm = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom Re = CC')
w.qed([w.s([], 'cnvimass', '%s C_ dom Re' % STR), dm], 'sseqtri', '%s C_ CC' % STR); run1(w)

# ---- crectstr --------------------------------------------------------------
LL = '( X + ( _i x. -u T ) )'; UR = '( Y + ( _i x. T ) )'
w = W('crectstr', 'A rectangle whose vertical sides are the strip boundaries lies in the strip.')
A0 = '( X e. RR /\\ Y e. RR /\\ T e. RR )'
A1 = '( %s /\\ v e. ( %s crect %s ) )' % (A0, LL, UR)
xr = w.s([], 'simp1', '( %s -> X e. RR )' % A0)
yr = w.s([], 'simp2', '( %s -> Y e. RR )' % A0)
tr = w.s([], 'simp3', '( %s -> T e. RR )' % A0)
ntr = w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)
llc = w.s([xr, ntr, w.inst('crcld')], 'syl2anc', '( %s -> %s e. CC )' % (A0, LL)) if False else None
ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
llc = w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % A0), w.s([ic, w.s([ntr], 'recnd', '( %s -> -u T e. CC )' % A0)], 'mulcld', '( %s -> ( _i x. -u T ) e. CC )' % A0)], 'addcld', '( %s -> %s e. CC )' % (A0, LL))
urc = w.s([w.s([yr], 'recnd', '( %s -> Y e. CC )' % A0), w.s([ic, w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'mulcld', '( %s -> ( _i x. T ) e. CC )' % A0)], 'addcld', '( %s -> %s e. CC )' % (A0, UR))
rll = w.s([xr, ntr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = X )' % (A0, LL))
rur = w.s([yr, tr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = Y )' % (A0, UR))
ill = w.s([xr, ntr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = -u T )' % (A0, LL))
iur = w.s([yr, tr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = T )' % (A0, UR))
vm = w.s([], 'simpr', '( %s -> v e. ( %s crect %s ) )' % (A1, LL, UR))
ec = w.s([vm, w.s([w.s([llc], 'adantr', '( %s -> %s e. CC )' % (A1, LL)), w.s([urc], 'adantr', '( %s -> %s e. CC )' % (A1, UR)), w.inst('elcrect')], 'syl2anc',
                  '( %s -> ( v e. ( %s crect %s ) <-> ( v e. CC /\\ ( Re ` v ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` v ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A1, LL, UR, LL, UR, LL, UR))],
          'mpbid', '( %s -> ( v e. CC /\\ ( Re ` v ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` v ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (A1, LL, UR, LL, UR))
vc = w.s([ec, w.inst('simp1')], 'syl', '( %s -> v e. CC )' % A1)
vre = w.s([ec, w.inst('simp2')], 'syl', '( %s -> ( Re ` v ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A1, LL, UR))
vre2 = w.s([vre, w.s([w.s([rll], 'adantr', '( %s -> ( Re ` %s ) = X )' % (A1, LL)), w.s([rur], 'adantr', '( %s -> ( Re ` %s ) = Y )' % (A1, UR))], 'oveq12d',
                     '( %s -> ( ( Re ` %s ) [,] ( Re ` %s ) ) = ( X [,] Y ) )' % (A1, LL, UR))], 'eleqtrd', '( %s -> ( Re ` v ) e. ( X [,] Y ) )' % A1)
mem = w.s([w.s([vc, vre2], 'jca', '( %s -> ( v e. CC /\\ ( Re ` v ) e. ( X [,] Y ) ) )' % A1),
           w.s([w.s([], 'elstr', '( v e. %s <-> ( v e. CC /\\ ( Re ` v ) e. ( X [,] Y ) ) )' % STR)], 'a1i',
               '( %s -> ( v e. %s <-> ( v e. CC /\\ ( Re ` v ) e. ( X [,] Y ) ) ) )' % (A1, STR))], 'mpbird',
          '( %s -> v e. %s )' % (A1, STR))
w.qed([w.s([mem], 'ex', '( %s -> ( v e. ( %s crect %s ) -> v e. %s ) )' % (A0, LL, UR, STR))], 'ssrdv',
      '( %s -> ( %s crect %s ) C_ %s )' % (A0, LL, UR, STR)); run1(w)

# ---- sqleabs2 --------------------------------------------------------------
SB = '( ( abs ` X ) + ( abs ` Y ) )'
w = W('sqleabs2', 'A point of a real interval has square below the square of the sum of the moduli of the endpoints.')
A0 = '( ( X e. RR /\\ Y e. RR /\\ V e. RR ) /\\ ( X <_ V /\\ V <_ Y ) )'
xr = w.s([], 'simpl1', '( %s -> X e. RR )' % A0)
yr = w.s([], 'simpl2', '( %s -> Y e. RR )' % A0)
vr = w.s([], 'simpl3', '( %s -> V e. RR )' % A0)
xv = w.s([], 'simprl', '( %s -> X <_ V )' % A0)
vy = w.s([], 'simprr', '( %s -> V <_ Y )' % A0)
nx, px, ax = absbnds(w, A0, 'X', xr)
ny, py, ay = absbnds(w, A0, 'Y', yr)
ax0 = w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % A0)], 'absge0d', '( %s -> 0 <_ ( abs ` X ) )' % A0)
ay0 = w.s([w.s([yr], 'recnd', '( %s -> Y e. CC )' % A0)], 'absge0d', '( %s -> 0 <_ ( abs ` Y ) )' % A0)
sbr = w.s([ax, ay], 'readdcld', '( %s -> %s e. RR )' % (A0, SB))
sb0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), ax, sbr, ax0,
           w.s([ay0, w.s([ax, ay, w.inst('addge01')], 'syl2anc', '( %s -> ( 0 <_ ( abs ` Y ) <-> ( abs ` X ) <_ %s ) )' % (A0, SB))], 'mpbid',
               '( %s -> ( abs ` X ) <_ %s )' % (A0, SB))], 'letrd', '( %s -> 0 <_ %s )' % (A0, SB))
axsb = w.s([ay0, w.s([ax, ay, w.inst('addge01')], 'syl2anc', '( %s -> ( 0 <_ ( abs ` Y ) <-> ( abs ` X ) <_ %s ) )' % (A0, SB))], 'mpbid', '( %s -> ( abs ` X ) <_ %s )' % (A0, SB))
aysb = w.s([ax0, w.s([ay, ax, w.inst('addge02')], 'syl2anc', '( %s -> ( 0 <_ ( abs ` X ) <-> ( abs ` Y ) <_ %s ) )' % (A0, SB))], 'mpbid', '( %s -> ( abs ` Y ) <_ %s )' % (A0, SB))
nsb = w.s([axsb, w.s([ax, sbr], 'lenegd', '( %s -> ( ( abs ` X ) <_ %s <-> -u %s <_ -u ( abs ` X ) ) )' % (A0, SB, SB))], 'mpbid',
          '( %s -> -u %s <_ -u ( abs ` X ) )' % (A0, SB))
nsbr = w.s([sbr], 'renegcld', '( %s -> -u %s e. RR )' % (A0, SB))
naxr = w.s([ax], 'renegcld', '( %s -> -u ( abs ` X ) e. RR )' % A0)
lo = w.s([nsbr, naxr, vr, nsb, w.s([naxr, xr, vr, nx, xv], 'letrd', '( %s -> -u ( abs ` X ) <_ V )' % A0)], 'letrd', '( %s -> -u %s <_ V )' % (A0, SB))
hi = w.s([vr, ay, sbr, w.s([vr, yr, ay, vy, py], 'letrd', '( %s -> V <_ ( abs ` Y ) )' % A0), aysb], 'letrd', '( %s -> V <_ %s )' % (A0, SB))
av = w.s([w.s([lo, hi], 'jca', '( %s -> ( -u %s <_ V /\\ V <_ %s ) )' % (A0, SB, SB)),
          w.s([vr, sbr, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` V ) <_ %s <-> ( -u %s <_ V /\\ V <_ %s ) ) )' % (A0, SB, SB, SB))],
         'mpbird', '( %s -> ( abs ` V ) <_ %s )' % (A0, SB))
avr = w.s([w.s([vr], 'recnd', '( %s -> V e. CC )' % A0)], 'abscld', '( %s -> ( abs ` V ) e. RR )' % A0)
av0 = w.s([w.s([vr], 'recnd', '( %s -> V e. CC )' % A0)], 'absge0d', '( %s -> 0 <_ ( abs ` V ) )' % A0)
sq = w.s([av, w.s([avr, sbr, av0, sb0], 'le2sqd', '( %s -> ( ( abs ` V ) <_ %s <-> ( ( abs ` V ) ^ 2 ) <_ ( %s ^ 2 ) ) )' % (A0, SB, SB))],
         'mpbid', '( %s -> ( ( abs ` V ) ^ 2 ) <_ ( %s ^ 2 ) )' % (A0, SB))
w.qed([w.s([w.s([vr, w.inst('absresq')], 'syl', '( %s -> ( ( abs ` V ) ^ 2 ) = ( V ^ 2 ) )' % A0)], 'eqcomd',
           '( %s -> ( V ^ 2 ) = ( ( abs ` V ) ^ 2 ) )' % A0), sq], 'eqbrtrd', '( %s -> ( V ^ 2 ) <_ ( %s ^ 2 ) )' % (A0, SB)); run1(w)

# ---- crectfre --------------------------------------------------------------
DISJ = '( ( ( Re ` u ) = %s \\/ ( Re ` u ) = %s ) \\/ ( ( Im ` u ) = %s \\/ ( Im ` u ) = %s ) )' % (RA, RB, IA, IB)
w = W('crectfre', 'Every point of the boundary frame of a rectangle has a coordinate equal to one of the four rectangle coordinates.')
A0 = '( %s /\\ %s )' % (AB, GEO)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
b1 = P10; a1 = P01
rb1 = w.s([br, ai, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, b1, RB))
ib1 = w.s([br, ai, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, b1, IA))
ra1 = w.s([ar, bi, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, a1, RA))
ia1 = w.s([ar, bi, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, a1, IB))
res = []
# edge 1: A cseg B1, horizontal at Im A
q1 = w.s([ac, cc[b1], w.s([ib1], 'eqcomd', '( %s -> %s = ( Im ` %s ) )' % (A0, IA, b1)), w.inst('cseghim')], 'syl3anc',
         '( %s -> A. u e. %s ( Im ` u ) = %s )' % (A0, SEGS[0], IA))
E1 = '( %s /\\ u e. %s )' % (A0, SEGS[0])
p1 = w.s([w.s([q1], 'adantr', '( %s -> A. u e. %s ( Im ` u ) = %s )' % (E1, SEGS[0], IA)), w.s([], 'simpr', '( %s -> u e. %s )' % (E1, SEGS[0])),
          w.inst('rspa')], 'syl2anc', '( %s -> ( Im ` u ) = %s )' % (E1, IA))
res.append(w.s([w.s([w.s([p1], 'orcd', '( %s -> ( ( Im ` u ) = %s \\/ ( Im ` u ) = %s ) )' % (E1, IA, IB))], 'olcd', '( %s -> %s )' % (E1, DISJ))],
               'ralrimiva', '( %s -> A. u e. %s %s )' % (A0, SEGS[0], DISJ)))
# edge 2: B1 cseg B, vertical at Re B
q2 = w.s([cc[b1], bc, w.s([rb1], 'idi', '( %s -> ( Re ` %s ) = %s )' % (A0, b1, RB)), w.inst('csegvre')], 'syl3anc',
         '( %s -> A. u e. %s ( Re ` u ) = ( Re ` %s ) )' % (A0, SEGS[1], b1))
E2s = '( %s /\\ u e. %s )' % (A0, SEGS[1])
p2a = w.s([w.s([q2], 'adantr', '( %s -> A. u e. %s ( Re ` u ) = ( Re ` %s ) )' % (E2s, SEGS[1], b1)), w.s([], 'simpr', '( %s -> u e. %s )' % (E2s, SEGS[1])),
           w.inst('rspa')], 'syl2anc', '( %s -> ( Re ` u ) = ( Re ` %s ) )' % (E2s, b1))
p2 = w.s([p2a, w.s([rb1], 'adantr', '( %s -> ( Re ` %s ) = %s )' % (E2s, b1, RB))], 'eqtrd', '( %s -> ( Re ` u ) = %s )' % (E2s, RB))
res.append(w.s([w.s([w.s([p2], 'olcd', '( %s -> ( ( Re ` u ) = %s \\/ ( Re ` u ) = %s ) )' % (E2s, RA, RB))], 'orcd', '( %s -> %s )' % (E2s, DISJ))],
               'ralrimiva', '( %s -> A. u e. %s %s )' % (A0, SEGS[1], DISJ)))
# edge 3: B cseg A1, horizontal at Im B
q3 = w.s([bc, cc[a1], w.s([ia1], 'eqcomd', '( %s -> %s = ( Im ` %s ) )' % (A0, IB, a1)), w.inst('cseghim')], 'syl3anc',
         '( %s -> A. u e. %s ( Im ` u ) = %s )' % (A0, SEGS[2], IB))
E3 = '( %s /\\ u e. %s )' % (A0, SEGS[2])
p3 = w.s([w.s([q3], 'adantr', '( %s -> A. u e. %s ( Im ` u ) = %s )' % (E3, SEGS[2], IB)), w.s([], 'simpr', '( %s -> u e. %s )' % (E3, SEGS[2])),
          w.inst('rspa')], 'syl2anc', '( %s -> ( Im ` u ) = %s )' % (E3, IB))
res.append(w.s([w.s([w.s([p3], 'olcd', '( %s -> ( ( Im ` u ) = %s \\/ ( Im ` u ) = %s ) )' % (E3, IA, IB))], 'olcd', '( %s -> %s )' % (E3, DISJ))],
               'ralrimiva', '( %s -> A. u e. %s %s )' % (A0, SEGS[2], DISJ)))
# edge 4: A1 cseg A, vertical at Re A
q4 = w.s([cc[a1], ac, w.s([ra1], 'idi', '( %s -> ( Re ` %s ) = %s )' % (A0, a1, RA)), w.inst('csegvre')], 'syl3anc',
         '( %s -> A. u e. %s ( Re ` u ) = ( Re ` %s ) )' % (A0, SEGS[3], a1))
E4 = '( %s /\\ u e. %s )' % (A0, SEGS[3])
p4a = w.s([w.s([q4], 'adantr', '( %s -> A. u e. %s ( Re ` u ) = ( Re ` %s ) )' % (E4, SEGS[3], a1)), w.s([], 'simpr', '( %s -> u e. %s )' % (E4, SEGS[3])),
           w.inst('rspa')], 'syl2anc', '( %s -> ( Re ` u ) = ( Re ` %s ) )' % (E4, a1))
p4 = w.s([p4a, w.s([ra1], 'adantr', '( %s -> ( Re ` %s ) = %s )' % (E4, a1, RA))], 'eqtrd', '( %s -> ( Re ` u ) = %s )' % (E4, RA))
res.append(w.s([w.s([w.s([p4], 'orcd', '( %s -> ( ( Re ` u ) = %s \\/ ( Re ` u ) = %s ) )' % (E4, RA, RB))], 'orcd', '( %s -> %s )' % (E4, DISJ))],
               'ralrimiva', '( %s -> A. u e. %s %s )' % (A0, SEGS[3], DISJ)))
U12 = '( %s u. %s )' % (SEGS[0], SEGS[1]); U34 = '( %s u. %s )' % (SEGS[2], SEGS[3])
c12 = w.s([w.s([res[0], res[1]], 'jca', '( %s -> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (A0, SEGS[0], DISJ, SEGS[1], DISJ)),
           w.s([w.s([], 'ralunb', '( A. u e. %s %s <-> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (U12, DISJ, SEGS[0], DISJ, SEGS[1], DISJ))], 'a1i',
               '( %s -> ( A. u e. %s %s <-> ( A. u e. %s %s /\\ A. u e. %s %s ) ) )' % (A0, U12, DISJ, SEGS[0], DISJ, SEGS[1], DISJ))],
          'mpbird', '( %s -> A. u e. %s %s )' % (A0, U12, DISJ))
c34 = w.s([w.s([res[2], res[3]], 'jca', '( %s -> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (A0, SEGS[2], DISJ, SEGS[3], DISJ)),
           w.s([w.s([], 'ralunb', '( A. u e. %s %s <-> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (U34, DISJ, SEGS[2], DISJ, SEGS[3], DISJ))], 'a1i',
               '( %s -> ( A. u e. %s %s <-> ( A. u e. %s %s /\\ A. u e. %s %s ) ) )' % (A0, U34, DISJ, SEGS[2], DISJ, SEGS[3], DISJ))],
          'mpbird', '( %s -> A. u e. %s %s )' % (A0, U34, DISJ))
w.qed([w.s([c12, c34], 'jca', '( %s -> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (A0, U12, DISJ, U34, DISJ)),
       w.s([w.s([], 'ralunb', '( A. u e. %s %s <-> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (FR, DISJ, U12, DISJ, U34, DISJ))], 'a1i',
           '( %s -> ( A. u e. %s %s <-> ( A. u e. %s %s /\\ A. u e. %s %s ) ) )' % (A0, FR, DISJ, U12, DISJ, U34, DISJ))],
      'mpbird', '( %s -> A. u e. %s %s )' % (A0, FR, DISJ)); run1(w)

# ---- explimle --------------------------------------------------------------
ALL = 'A. e e. RR+ A <_ ( C x. ( exp ` ( e x. J ) ) )'
w = W('explimle', 'A real below C times exp ( e J ) for every positive e, with J nonnegative, is below C.')
A0 = '( A e. RR /\\ C e. RR+ /\\ ( ( J e. RR /\\ 0 <_ J ) /\\ %s ) )' % ALL
Q1 = '( %s /\\ x e. RR+ )' % A0
L = '( 1 + ( x / C ) )'
LG = '( log ` %s )' % L
J1 = '( J + 1 )'
EE = '( %s / ( 2 x. %s ) )' % (LG, J1)
ar = w.s([], 'simp1', '( %s -> A e. RR )' % A0)
crp = w.s([], 'simp2', '( %s -> C e. RR+ )' % A0)
jl = w.s([], 'simp3', '( %s -> ( ( J e. RR /\\ 0 <_ J ) /\\ %s ) )' % (A0, ALL))
j0 = w.s([jl, w.inst('simpl')], 'syl', '( %s -> ( J e. RR /\\ 0 <_ J ) )' % A0)
al = w.s([jl, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALL))
jr = w.s([j0, w.inst('simpl')], 'syl', '( %s -> J e. RR )' % A0)
jge = w.s([j0, w.inst('simpr')], 'syl', '( %s -> 0 <_ J )' % A0)
cr = w.s([crp], 'rpred', '( %s -> C e. RR )' % A0)
# under ( A0 /\ x e. RR+ )
xrp = w.s([], 'simpr', '( %s -> x e. RR+ )' % Q1)
arq = w.s([ar], 'adantr', '( %s -> A e. RR )' % Q1)
crpq = w.s([crp], 'adantr', '( %s -> C e. RR+ )' % Q1)
crq = w.s([cr], 'adantr', '( %s -> C e. RR )' % Q1)
jrq = w.s([jr], 'adantr', '( %s -> J e. RR )' % Q1)
jgeq = w.s([jge], 'adantr', '( %s -> 0 <_ J )' % Q1)
alq = w.s([al], 'adantr', '( %s -> %s )' % (Q1, ALL))
xcrp = w.s([xrp, crpq], 'rpdivcld', '( %s -> ( x / C ) e. RR+ )' % Q1)
one = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Q1), xcrp, w.inst('ltaddrp')], 'syl2anc', '( %s -> 1 < %s )' % (Q1, L))
lrp = w.s([w.s([], '1rp', '1 e. RR+'), xcrp], 'rpaddcld', '( %s -> %s e. RR+ )' % (Q1, L)) if False else w.s(
    [w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % Q1), xcrp], 'rpaddcld', '( %s -> %s e. RR+ )' % (Q1, L))
lr = w.s([lrp], 'rpred', '( %s -> %s e. RR )' % (Q1, L))
lgrp = w.s([lr, one, w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (Q1, LG))
lgr = w.s([lgrp], 'rpred', '( %s -> %s e. RR )' % (Q1, LG))
j1rp = w.s([jrq, jgeq, w.s([], '1red', '( %s -> 1 e. RR )' % Q1)], 'idi', 'x') if False else None
j1r = w.s([jrq, w.s([], '1red', '( %s -> 1 e. RR )' % Q1)], 'readdcld', '( %s -> %s e. RR )' % (Q1, J1))
j1p = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Q1), jrq, j1r, jgeq,
           w.s([jrq, w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % Q1), w.inst('ltaddrp')], 'syl2anc', '( %s -> J < %s )' % (Q1, J1))],
          'lelttrd', '( %s -> 0 < %s )' % (Q1, J1))
j1rp = w.s([j1r, j1p], 'elrpd', '( %s -> %s e. RR+ )' % (Q1, J1))
t2rp = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % Q1)
den = w.s([t2rp, j1rp], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (Q1, J1))
eerp = w.s([lgrp, den], 'rpdivcld', '( %s -> %s e. RR+ )' % (Q1, EE))
eer = w.s([eerp], 'rpred', '( %s -> %s e. RR )' % (Q1, EE))
# ( EE x. J ) <_ ( EE x. ( J + 1 ) )
jlej1 = w.s([jgeq, w.s([jrq, w.s([], '1red', '( %s -> 1 e. RR )' % Q1)], 'idi', '( %s -> J e. RR )' % Q1)], 'idi', '( %s -> 0 <_ J )' % Q1) if False else None
jj1 = w.s([w.s([], '0le1', '0 <_ 1'), w.s([jrq, w.s([], '1red', '( %s -> 1 e. RR )' % Q1), w.inst('addge01')], 'syl2anc',
                                          '( %s -> ( 0 <_ 1 <-> J <_ %s ) )' % (Q1, J1))], 'mpbii', '( %s -> J <_ %s )' % (Q1, J1)) if False else w.s(
    [w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % Q1),
     w.s([jrq, w.s([], '1red', '( %s -> 1 e. RR )' % Q1), w.inst('addge01')], 'syl2anc', '( %s -> ( 0 <_ 1 <-> J <_ %s ) )' % (Q1, J1))],
    'mpbid', '( %s -> J <_ %s )' % (Q1, J1))
m1 = w.s([jj1, w.s([jrq, j1r, eerp], 'lemul2d', '( %s -> ( J <_ %s <-> ( %s x. J ) <_ ( %s x. %s ) ) )' % (Q1, J1, EE, EE, J1))], 'mpbid',
         '( %s -> ( %s x. J ) <_ ( %s x. %s ) )' % (Q1, EE, EE, J1))
# ( EE x. ( J + 1 ) ) = ( LG / 2 )
lgc = w.s([lgr], 'recnd', '( %s -> %s e. CC )' % (Q1, LG))
j1c = w.s([j1r], 'recnd', '( %s -> %s e. CC )' % (Q1, J1))
j1ne = w.s([j1rp], 'rpne0d', '( %s -> %s =/= 0 )' % (Q1, J1))
t2c = w.s([], '2cnd', '( %s -> 2 e. CC )' % Q1)
t2ne = w.s([t2rp], 'rpne0d', '( %s -> 2 =/= 0 )' % Q1)
dd1 = w.s([w.s([lgc, t2c, j1c, t2ne, j1ne], 'divdiv1d', '( %s -> ( ( %s / 2 ) / %s ) = ( %s / ( 2 x. %s ) ) )' % (Q1, LG, J1, LG, J1))], 'eqcomd',
          '( %s -> %s = ( ( %s / 2 ) / %s ) )' % (Q1, EE, LG, J1))
dd2 = w.s([w.s([dd1], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( ( %s / 2 ) / %s ) x. %s ) )' % (Q1, EE, J1, LG, J1, J1)),
           w.s([w.s([lgc, t2c, t2ne], 'divcld', '( %s -> ( %s / 2 ) e. CC )' % (Q1, LG)), j1c, j1ne], 'divcan1d',
               '( %s -> ( ( ( %s / 2 ) / %s ) x. %s ) = ( %s / 2 ) )' % (Q1, LG, J1, J1, LG))], 'eqtrd',
          '( %s -> ( %s x. %s ) = ( %s / 2 ) )' % (Q1, EE, J1, LG))
hlt = w.s([w.s([lgrp], 'rpgt0d', '( %s -> 0 < %s )' % (Q1, LG)), w.s([lgr, w.inst('halfpos')], 'syl', '( %s -> ( 0 < %s <-> ( %s / 2 ) < %s ) )' % (Q1, LG, LG, LG))],
          'mpbid', '( %s -> ( %s / 2 ) < %s )' % (Q1, LG, LG))
m2 = w.s([dd2, hlt], 'eqbrtrd', '( %s -> ( %s x. %s ) < %s )' % (Q1, EE, J1, LG))
eejr = w.s([eer, jrq], 'remulcld', '( %s -> ( %s x. J ) e. RR )' % (Q1, EE))
eej1r = w.s([eer, j1r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Q1, EE, J1))
klt = w.s([eejr, eej1r, lgr, m1, m2], 'lelttrd', '( %s -> ( %s x. J ) < %s )' % (Q1, EE, LG))
eflt_ = w.s([klt, w.s([eejr, lgr, w.inst('eflt')], 'syl2anc', '( %s -> ( ( %s x. J ) < %s <-> ( exp ` ( %s x. J ) ) < ( exp ` %s ) ) )' % (Q1, EE, LG, EE, LG))],
            'mpbid', '( %s -> ( exp ` ( %s x. J ) ) < ( exp ` %s ) )' % (Q1, EE, LG))
efl = w.s([eflt_, w.s([lrp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = %s )' % (Q1, LG, L))], 'breqtrd',
          '( %s -> ( exp ` ( %s x. J ) ) < %s )' % (Q1, EE, L))
# instantiate the hypothesis at EE
sub = w.s([w.s([w.s([w.s([], 'oveq1', '( e = %s -> ( e x. J ) = ( %s x. J ) )' % (EE, EE))], 'fveq2d',
                    '( e = %s -> ( exp ` ( e x. J ) ) = ( exp ` ( %s x. J ) ) )' % (EE, EE))], 'oveq2d',
               '( e = %s -> ( C x. ( exp ` ( e x. J ) ) ) = ( C x. ( exp ` ( %s x. J ) ) ) )' % (EE, EE))], 'breq2d',
          '( e = %s -> ( A <_ ( C x. ( exp ` ( e x. J ) ) ) <-> A <_ ( C x. ( exp ` ( %s x. J ) ) ) ) )' % (EE, EE))
inst = w.s([sub, alq, eerp], 'rspcdva', '( %s -> A <_ ( C x. ( exp ` ( %s x. J ) ) ) )' % (Q1, EE))
efr = w.s([eejr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( %s x. J ) ) e. RR )' % (Q1, EE))
cmul = w.s([efl, w.s([efr, lr, crpq], 'ltmul2d', '( %s -> ( ( exp ` ( %s x. J ) ) < %s <-> ( C x. ( exp ` ( %s x. J ) ) ) < ( C x. %s ) ) )' % (Q1, EE, L, EE, L))],
           'mpbid', '( %s -> ( C x. ( exp ` ( %s x. J ) ) ) < ( C x. %s ) )' % (Q1, EE, L))
cc_ = w.s([crq], 'recnd', '( %s -> C e. CC )' % Q1)
xc = w.s([w.s([xrp], 'rpred', '( %s -> x e. RR )' % Q1)], 'recnd', '( %s -> x e. CC )' % Q1)
cne = w.s([crpq], 'rpne0d', '( %s -> C =/= 0 )' % Q1)
cl1 = w.s([w.s([cc_, w.s([], '1cnd', '( %s -> 1 e. CC )' % Q1), w.s([xc, cc_, cne], 'divcld', '( %s -> ( x / C ) e. CC )' % Q1)], 'adddid',
                '( %s -> ( C x. %s ) = ( ( C x. 1 ) + ( C x. ( x / C ) ) ) )' % (Q1, L)),
           w.s([w.s([cc_], 'mulridd', '( %s -> ( C x. 1 ) = C )' % Q1), w.s([xc, cc_, cne], 'divcan2d', '( %s -> ( C x. ( x / C ) ) = x )' % Q1)], 'oveq12d',
               '( %s -> ( ( C x. 1 ) + ( C x. ( x / C ) ) ) = ( C + x ) )' % Q1)], 'eqtrd', '( %s -> ( C x. %s ) = ( C + x ) )' % (Q1, L))
fin = w.s([w.s([cmul, cl1], 'breqtrd', '( %s -> ( C x. ( exp ` ( %s x. J ) ) ) < ( C + x ) )' % (Q1, EE))], 'idi',
          '( %s -> ( C x. ( exp ` ( %s x. J ) ) ) < ( C + x ) )' % (Q1, EE))
cef = w.s([crq, efr], 'remulcld', '( %s -> ( C x. ( exp ` ( %s x. J ) ) ) e. RR )' % (Q1, EE))
cxr = w.s([crq, w.s([xrp], 'rpred', '( %s -> x e. RR )' % Q1)], 'readdcld', '( %s -> ( C + x ) e. RR )' % Q1)
lex = w.s([w.s([arq, cef, cxr, inst, fin], 'lelttrd', '( %s -> A < ( C + x ) )' % Q1)], 'ltled', '( %s -> A <_ ( C + x ) )' % Q1)
allx = w.s([lex], 'ralrimiva', '( %s -> A. x e. RR+ A <_ ( C + x ) )' % A0)
w.qed([allx, w.s([ar, cr, w.inst('alrple')], 'syl2anc', '( %s -> ( A <_ C <-> A. x e. RR+ A <_ ( C + x ) ) )' % A0)], 'mpbird',
      '( %s -> A <_ C )' % A0); run1(w)
