"""Sortie C0, batch 2: continuity and integrability of the parametrised integrand, lintval, lintcl, dvcseglin."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ---- unitioo, unitntr
w = W('unitioo', 'The open unit interval is open in the topology of the reals as a subspace of the complex numbers.')
i = w.s([], 'iooretop', '( 0 (,) 1 ) e. ( topGen ` ran (,) )')
e = w.s([], 'eqid', '%s = %s' % (TOP, TOP)); t = w.s([e], 'tgioo2', '( topGen ` ran (,) ) = %s' % JR)
w.qed([i, t], 'eleqtri', '( 0 (,) 1 ) e. %s' % JR); run(w)

w = W('unitntr', 'The interior of the closed unit interval in the topology of the reals as a subspace of the complex numbers.')
r0 = w.s([], '0re', '0 e. RR'); r1 = w.s([], '1re', '1 e. RR')
ic = w.s([r0, r1, w.inst('iccntr')], 'mp2an', '( ( int ` ( topGen ` ran (,) ) ) ` ( 0 [,] 1 ) ) = ( 0 (,) 1 )')
e = w.s([], 'eqid', '%s = %s' % (TOP, TOP)); t = w.s([e], 'tgioo2', '( topGen ` ran (,) ) = %s' % JR)
t2 = w.s([t], 'fveq2i', '( int ` ( topGen ` ran (,) ) ) = ( int ` %s )' % JR)
t3 = w.s([t2], 'fveq1i', '( ( int ` ( topGen ` ran (,) ) ) ` ( 0 [,] 1 ) ) = ( ( int ` %s ) ` ( 0 [,] 1 ) )' % JR)
w.qed([t3, ic], 'eqtr3i', '( ( int ` %s ) ` ( 0 [,] 1 ) ) = ( 0 (,) 1 )' % JR); run(w)

# ---- cseglincn
w = W('cseglincn', 'The parametrisation of a segment is continuous on a set of reals.')
A = '( A e. CC /\\ B e. CC /\\ X C_ RR )'
a = w.s([], 'simp1', '( %s -> A e. CC )' % A); b = w.s([], 'simp2', '( %s -> B e. CC )' % A); x = w.s([], 'simp3', '( %s -> X C_ RR )' % A)
rc = closed(w, A, 'ax-resscn', 'RR C_ CC'); xc = w.s([x, rc], 'sstrd', '( %s -> X C_ CC )' % A)
cc = w.s([], 'ssidd', '( %s -> CC C_ CC )' % A)
mc = w.s([a, xc, cc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. X |-> A ) e. ( X -cn-> CC ) )' % A)
mi = w.s([xc, cc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. X |-> t ) e. ( X -cn-> CC ) )' % A)
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A)
mba = w.s([ba, xc, cc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. X |-> ( B - A ) ) e. ( X -cn-> CC ) )' % A)
e, mul = cnop(w, A, 'x.')
pr = w.s([e, mul, mi, mba], 'cncfmpt2f', '( %s -> ( t e. X |-> ( t x. ( B - A ) ) ) e. ( X -cn-> CC ) )' % A)
e2, add = cnop(w, A, '+')
w.qed([e2, add, mc, pr], 'cncfmpt2f', '( %s -> ( t e. X |-> %s ) e. ( X -cn-> CC ) )' % (A, LIN('A', 'B'))); run(w)

# ---- cseglincnd
w = W('cseglincnd', 'The parametrisation of a segment is continuous into a set containing the segment.')
A = '( ( A e. CC /\\ B e. CC ) /\\ ( D C_ CC /\\ ( A cseg B ) C_ D ) /\\ X C_ ( 0 [,] 1 ) )'; A2 = '( %s /\\ t e. X )' % A
a = w.s([], 'simp1l', '( %s -> A e. CC )' % A); b = w.s([], 'simp1r', '( %s -> B e. CC )' % A)
dc = w.s([], 'simp2l', '( %s -> D C_ CC )' % A); sg = w.s([], 'simp2r', '( %s -> ( A cseg B ) C_ D )' % A); x = w.s([], 'simp3', '( %s -> X C_ ( 0 [,] 1 ) )' % A)
us = closed(w, A, 'unitssre', '( 0 [,] 1 ) C_ RR'); xr = w.s([x, us], 'sstrd', '( %s -> X C_ RR )' % A)
cn = w.s([a, b, xr, w.inst('cseglincn')], 'syl3anc', '( %s -> ( t e. X |-> %s ) e. ( X -cn-> CC ) )' % (A, LIN('A', 'B')))
a2 = w.s([a], 'adantr', '( %s -> A e. CC )' % A2); b2 = w.s([b], 'adantr', '( %s -> B e. CC )' % A2)
x2 = w.s([x], 'adantr', '( %s -> X C_ ( 0 [,] 1 ) )' % A2); tt = w.s([], 'simpr', '( %s -> t e. X )' % A2); t01 = w.s([x2, tt], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % A2)
l = w.s([a2, b2, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (A2, LIN('A', 'B')))
sg2 = w.s([sg], 'adantr', '( %s -> ( A cseg B ) C_ D )' % A2); ld = w.s([sg2, l], 'sseldd', '( %s -> %s e. D )' % (A2, LIN('A', 'B')))
fm = w.s([ld], 'fmptd', '( %s -> ( t e. X |-> %s ) : X --> D )' % (A, LIN('A', 'B')))
bi = w.s([dc, cn, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( ( t e. X |-> %s ) e. ( X -cn-> D ) <-> ( t e. X |-> %s ) : X --> D ) )' % (A, LIN('A', 'B'), LIN('A', 'B')))
w.qed([fm, bi], 'mpbird', '( %s -> ( t e. X |-> %s ) e. ( X -cn-> D ) )' % (A, LIN('A', 'B'))); run(w)

# ---- cseglincnf
w = W('cseglincnf', 'A continuous function composed with the parametrisation of a segment in its domain is continuous.')
A = '( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) /\\ X C_ ( 0 [,] 1 ) )'
a = w.s([], 'simp1l', '( %s -> A e. CC )' % A); b = w.s([], 'simp1r', '( %s -> B e. CC )' % A)
f = w.s([], 'simp2l', '( %s -> F e. ( D -cn-> CC ) )' % A); sg = w.s([], 'simp2r', '( %s -> ( A cseg B ) C_ D )' % A); x = w.s([], 'simp3', '( %s -> X C_ ( 0 [,] 1 ) )' % A)
dc = w.s([f, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A)
ab = w.s([a, b], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A); dg = w.s([dc, sg], 'jca', '( %s -> ( D C_ CC /\\ ( A cseg B ) C_ D ) )' % A)
d1 = w.s([ab, dg, x, w.inst('cseglincnd')], 'syl3anc', '( %s -> ( t e. X |-> %s ) e. ( X -cn-> D ) )' % (A, LIN('A', 'B')))
ff = w.s([f, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A); fm = w.s([ff], 'feqmptd', '( %s -> F = ( y e. D |-> ( F ` y ) ) )' % A)
fcn = w.s([f, fm], 'eqeltrrd', '( %s -> ( y e. D |-> ( F ` y ) ) e. ( D -cn-> CC ) )' % A)
nf = w.s([], 'nfv', 'F/ t %s' % A); si = w.s([], 'ssidd', '( %s -> D C_ D )' % A)
sb = w.s([], 'fveq2', '( y = %s -> ( F ` y ) = ( F ` %s ) )' % (LIN('A', 'B'), LIN('A', 'B')))
w.qed([nf, d1, fcn, si, sb], 'cncfcompt2', '( %s -> ( t e. X |-> ( F ` %s ) ) e. ( X -cn-> CC ) )' % (A, LIN('A', 'B'))); run(w)

# ---- lintcnlem
w = W('lintcnlem', 'The integrand of a segment integral is continuous on a subset of the unit interval.')
A = '( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) /\\ X C_ ( 0 [,] 1 ) )'
a = w.s([], 'simp1l', '( %s -> A e. CC )' % A); b = w.s([], 'simp1r', '( %s -> B e. CC )' % A); x = w.s([], 'simp3', '( %s -> X C_ ( 0 [,] 1 ) )' % A)
c1 = w.s([], 'cseglincnf', '( %s -> ( t e. X |-> ( F ` %s ) ) e. ( X -cn-> CC ) )' % (A, LIN('A', 'B')))
us = closed(w, A, 'unitsscn', '( 0 [,] 1 ) C_ CC'); xc = w.s([x, us], 'sstrd', '( %s -> X C_ CC )' % A); cc = w.s([], 'ssidd', '( %s -> CC C_ CC )' % A)
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A)
mba = w.s([ba, xc, cc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. X |-> ( B - A ) ) e. ( X -cn-> CC ) )' % A)
e, mul = cnop(w, A, 'x.')
w.qed([e, mul, c1, mba], 'cncfmpt2f', '( %s -> ( t e. X |-> %s ) e. ( X -cn-> CC ) )' % (A, INTG('F', 'A', 'B'))); run(w)

# ---- lintibl
w = W('lintibl', 'The integrand of a segment integral is integrable on the open unit interval.')
A = PH; A2 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A
a, b, f, g = phctx(w, A)
ab = w.s([a, b], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A); fg = w.s([f, g], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % A)
si = w.s([], 'ssidd', '( %s -> ( 0 [,] 1 ) C_ ( 0 [,] 1 ) )' % A)
cn = w.s([ab, fg, si, w.inst('lintcnlem')], 'syl3anc', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (A, INTG('F', 'A', 'B')))
r0 = w.s([], '0red', '( %s -> 0 e. RR )' % A); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % A)
ib = w.s([r0, r1, cn, w.inst('cniccibl')], 'syl3anc', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) e. L^1 )' % (A, INTG('F', 'A', 'B')))
ss = closed(w, A, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )'); mb = closed(w, A, 'ioombl', '( 0 (,) 1 ) e. dom vol')
a2, b2, f2, g2 = phctx(w, A2, True); t01 = w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A2)
cl = intgcl(w, A2, a2, b2, f2, g2, t01)
w.qed([ss, mb, cl, ib], 'iblss', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) e. L^1 )' % (A, INTG('F', 'A', 'B'))); run(w)

# ---- lintval
w = W('lintval', 'Value of the integral of a function along a segment.')
A = '( F e. V /\\ A e. CC /\\ B e. CC )'; E = '( f = F /\\ p = <. A , B >. )'
f = w.s([], 'simp1', '( %s -> F e. V )' % A); a = w.s([], 'simp2', '( %s -> A e. CC )' % A); b = w.s([], 'simp3', '( %s -> B e. CC )' % A)
R = '( ( f ` ( ( 1st ` p ) + ( t x. ( ( 2nd ` p ) - ( 1st ` p ) ) ) ) ) x. ( ( 2nd ` p ) - ( 1st ` p ) ) )'
d = w.s([], 'df-lint', 'lint = ( f e. _V , p e. ( CC X. CC ) |-> S. ( 0 (,) 1 ) %s _d t )' % R)
dd = w.s([d], 'a1i', '( %s -> lint = ( f e. _V , p e. ( CC X. CC ) |-> S. ( 0 (,) 1 ) %s _d t ) )' % (A, R))
lf = w.s([], 'simpl', '( %s -> f = F )' % E); lp = w.s([], 'simpr', '( %s -> p = <. A , B >. )' % E)
c, R1 = w.congr(R, {'f': 'F', 'p': '<. A , B >.'}, E, {'f': lf, 'p': lp})
c2 = w.s([c], 'adantr', '( ( %s /\\ t e. ( 0 (,) 1 ) ) -> %s = %s )' % (E, R, R1))
c3 = w.s([c2], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (E, R, R1))
c4 = w.s([c3], 'adantl', '( ( %s /\\ %s ) -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (A, E, R, R1))
ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A); bx = w.s([b], 'elexd', '( %s -> B e. _V )' % A)
ev, R2 = evaluate(w, A, R1, {'A': ax, 'B': bx})
assert R2 == INTG('F', 'A', 'B'), R2
ev2 = w.s([ev], 'adantr', '( ( %s /\\ t e. ( 0 (,) 1 ) ) -> %s = %s )' % (A, R1, R2))
ev3 = w.s([ev2], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (A, R1, R2))
ev4 = w.s([ev3], 'adantr', '( ( %s /\\ %s ) -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (A, E, R1, R2))
c5 = w.s([c4, ev4], 'eqtrd', '( ( %s /\\ %s ) -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (A, E, R, R2))
fx = w.s([f], 'elexd', '( %s -> F e. _V )' % A)
op = w.s([a, b, w.inst('opelxpi')], 'syl2anc', '( %s -> <. A , B >. e. ( CC X. CC ) )' % A)
ix = closed(w, A, 'itgex', 'S. ( 0 (,) 1 ) %s _d t e. _V' % R2)
w.qed([dd, c5, fx, op, ix], 'ovmpod', '( %s -> ( F lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A, R2)); run(w)

# ---- lintcl
w = W('lintcl', 'Closure of the integral along a segment of a function continuous on a set containing the segment.')
A = PH; A2 = '( %s /\\ t e. ( 0 (,) 1 ) )' % A
a, b, f, g = phctx(w, A)
v = w.s([f, a, b, w.inst('lintval')], 'syl3anc', '( %s -> %s = %s )' % (A, LINT('F', 'A', 'B'), ITG(O01, INTG('F', 'A', 'B'))))
a2, b2, f2, g2 = phctx(w, A2, True); to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % A2)
ss = closed(w, A2, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )'); t01 = w.s([ss, to], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % A2)
cl = intgcl(w, A2, a2, b2, f2, g2, t01)
ib = w.s([], 'lintibl', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) e. L^1 )' % (A, INTG('F', 'A', 'B')))
ic = w.s([cl, ib], 'itgcl', '( %s -> %s e. CC )' % (A, ITG(O01, INTG('F', 'A', 'B'))))
w.qed([v, ic], 'eqeltrd', '( %s -> %s e. CC )' % (A, LINT('F', 'A', 'B'))); run(w)

# ---- dvcseglin
w = W('dvcseglin', 'The derivative of the parametrisation of a segment on the open unit interval is the constant B - A.')
A = '( A e. CC /\\ B e. CC )'; AR = '( %s /\\ t e. RR )' % A; AO = '( %s /\\ t e. ( 0 (,) 1 ) )' % A
a = w.s([], 'simpl', '( %s -> A e. CC )' % A); b = w.s([], 'simpr', '( %s -> B e. CC )' % A); ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A)
rr = closed(w, A, 'reelprrecn', 'RR e. { RR , CC }')
dc = w.s([rr, a], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> A ) ) = ( t e. RR |-> 0 ) )' % A)
di = w.s([rr], 'dvmptid', '( %s -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )' % A)
dba = w.s([rr, ba], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> ( B - A ) ) ) = ( t e. RR |-> 0 ) )' % A)
tr = w.s([], 'simpr', '( %s -> t e. RR )' % AR); tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % AR)
c1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % AR); c0 = w.s([], '0cnd', '( %s -> 0 e. CC )' % AR)
bar = w.s([ba], 'adantr', '( %s -> ( B - A ) e. CC )' % AR); ar = w.s([a], 'adantr', '( %s -> A e. CC )' % AR)
dm = w.s([rr, tc, c1, di, bar, c0, dba], 'dvmptmul', '( %s -> ( RR _D ( t e. RR |-> ( t x. ( B - A ) ) ) ) = ( t e. RR |-> ( ( 1 x. ( B - A ) ) + ( 0 x. t ) ) ) )' % A)
tba = w.s([tc, bar], 'mulcld', '( %s -> ( t x. ( B - A ) ) e. CC )' % AR)
X = '( ( 1 x. ( B - A ) ) + ( 0 x. t ) )'
x1 = w.s([c1, bar], 'mulcld', '( %s -> ( 1 x. ( B - A ) ) e. CC )' % AR); x2 = w.s([c0, tc], 'mulcld', '( %s -> ( 0 x. t ) e. CC )' % AR)
xc = w.s([x1, x2], 'addcld', '( %s -> %s e. CC )' % (AR, X))
da = w.s([rr, ar, c0, dc, tba, xc, dm], 'dvmptadd', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( 0 + %s ) ) )' % (A, LIN('A', 'B'), X))
lc = w.s([ar, tba], 'addcld', '( %s -> %s e. CC )' % (AR, LIN('A', 'B'))); zx = w.s([c0, xc], 'addcld', '( %s -> ( 0 + %s ) e. CC )' % (AR, X))
oss = closed(w, A, 'ioossre', '( 0 (,) 1 ) C_ RR'); ej = w.s([], 'eqid', '%s = %s' % (JR, JR)); ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
uo = closed(w, A, 'unitioo', '( 0 (,) 1 ) e. %s' % JR)
dr = w.s([rr, lc, zx, da, oss, ej, ek, uo], 'dvmptres', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( 0 + %s ) ) )' % (A, LIN('A', 'B'), X))
# simplify the value
bao = w.s([ba], 'adantr', '( %s -> ( B - A ) e. CC )' % AO); to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AO)
tor = w.s([to, w.inst('elioore')], 'syl', '( %s -> t e. RR )' % AO); toc = w.s([tor], 'recnd', '( %s -> t e. CC )' % AO)
m1 = w.s([bao], 'mullidd', '( %s -> ( 1 x. ( B - A ) ) = ( B - A ) )' % AO); m0 = w.s([toc], 'mul02d', '( %s -> ( 0 x. t ) = 0 )' % AO)
m2 = w.s([m1, m0], 'oveq12d', '( %s -> %s = ( ( B - A ) + 0 ) )' % (AO, X)); m3 = w.s([bao], 'addridd', '( %s -> ( ( B - A ) + 0 ) = ( B - A ) )' % AO)
m4 = w.s([m2, m3], 'eqtrd', '( %s -> %s = ( B - A ) )' % (AO, X)); m5 = w.s([m4], 'oveq2d', '( %s -> ( 0 + %s ) = ( 0 + ( B - A ) ) )' % (AO, X))
m6 = w.s([bao], 'addlidd', '( %s -> ( 0 + ( B - A ) ) = ( B - A ) )' % AO); m7 = w.s([m5, m6], 'eqtrd', '( %s -> ( 0 + %s ) = ( B - A ) )' % (AO, X))
mp = w.s([m7], 'mpteq2dva', '( %s -> ( t e. ( 0 (,) 1 ) |-> ( 0 + %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( B - A ) ) )' % (A, X))
w.qed([dr, mp], 'eqtrd', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( B - A ) ) )' % (A, LIN('A', 'B'))); run(w)
