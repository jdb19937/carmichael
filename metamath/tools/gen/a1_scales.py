"""Sortie A1, batch 3: the scales zscale, yscaleE, yscale, Tscale and the reservoirs goodPrimesE, goodPrimes: values, closures, the two Lean equations."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

E2 = lambda N: '( ell2 ` %s )' % N
E3 = lambda N: '( ell3 ` %s )' % N
UZ = lambda k, N: '%s e. ( ZZ>= ` %s )' % (N, k)
ZR = lambda C, N: '( ( %s x. %s ) x. %s )' % (C, E2(N), E3(N))
NC = lambda X: '( Nceil ` %s )' % X
ZS = lambda C, N: '( %s zscale %s )' % (C, N)
Q99 = '( ; 9 9 / ; ; 1 0 0 )'
YEB = lambda C, N, E: NC('( %s ^c ( 1 - %s ) )' % (ZS(C, N), E))       # body of yscaleE
YEM = lambda C, N: '( e e. RR |-> %s )' % YEB(C, N, 'e')             # the curried mapping
YE = lambda C, N, E: '( ( %s yscaleE %s ) ` %s )' % (C, N, E)
YB = lambda C, N: NC('( %s ^c ( 2 / 3 ) )' % ZS(C, N))
YS = lambda C, N: '( %s yscale %s )' % (C, N)
TB = lambda N: NC('( 3 x. %s )' % E2(N))
TS = lambda N: '( Tscale ` %s )' % N
SMOOTH = lambda Y: 'A. p e. Prime ( p || ( q - 1 ) -> p <_ %s )' % Y
RAB = lambda C, N, Y: '{ q e. ( 0 ... %s ) | ( q e. Prime /\\ ( %s ^c %s ) < q /\\ %s ) }' % (ZS(C, N), ZS(C, N), Q99, SMOOTH(Y))
GEM = lambda C, N: '( e e. RR |-> %s )' % RAB(C, N, YE(C, N, 'e'))
GE = lambda C, N, E: '( ( %s goodPrimesE %s ) ` %s )' % (C, N, E)
GP = lambda C, N: '( %s goodPrimes %s )' % (C, N)
A2 = '( C e. RR /\\ N e. NN0 )'
A3 = '( C e. RR /\\ N e. NN0 /\\ E e. RR )'


def mpo_val(w, df, name, BODY, exsteps):
    """( ( C e. RR /\ N e. NN0 ) -> ( C name N ) = BODY(C,N) ) by ovmpoa; exsteps(w) returns the step BODY(C,N) e. _V"""
    A = '( c = C /\\ n = N )'
    l1 = w.s([], 'simpl', '( %s -> c = C )' % A); l2 = w.s([], 'simpr', '( %s -> n = N )' % A)
    c, b = w.congr(BODY('c', 'n'), {'c': 'C', 'n': 'N'}, A, {'c': l1, 'n': l2}); assert b == BODY('C', 'N'), b
    d = w.s([], df, '%s = ( c e. RR , n e. NN0 |-> %s )' % (name, BODY('c', 'n')))
    x = exsteps(w)
    return w.s([c, d, x], 'ovmpoa', '( %s -> ( C %s N ) = %s )' % (A2, name, BODY('C', 'N')))

def qedlast(w):
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]

# ---- zscaleval
w = W('zscaleval', 'Value of zscale: the natural ceiling of C * ell2 N * ell3 N (Lean: zscale).')
mpo_val(w, 'df-zscale', 'zscale', lambda c, n: NC(ZR(c, n)), lambda w: w.s([], 'fvex', '%s e. _V' % NC(ZR('C', 'N')))); qedlast(w); run(w)

def n0of3(w, A, n3, X='N'):
    u2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> %s )' % (A, UZ('2', X)))
    nn = w.s([u2, w.inst('eluz2nn')], 'syl', '( %s -> %s e. NN )' % (A, X))
    return u2, w.s([nn], 'nnnn0d', '( %s -> %s e. NN0 )' % (A, X))

def zreal(w, A, c, n3):
    """steps: ZR(C,N) e. RR from C e. RR and N e. ( ZZ>= ` 3 )"""
    u2, n0 = n0of3(w, A, n3)
    e2 = w.s([u2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, E2('N')))
    e3 = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, E3('N')))
    m1 = w.s([c, e2], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (A, E2('N')))
    return n0, w.s([m1, e3], 'remulcld', '( %s -> %s e. RR )' % (A, ZR('C', 'N')))

B3 = '( C e. RR /\\ %s )' % UZ('3', 'N')
w = W('zscalecl', 'Closure of zscale: a nonnegative integer for N >= 3 (where ell2 N and ell3 N are real).')
c = w.s([], 'simpl', '( %s -> C e. RR )' % B3); n3 = w.s([], 'simpr', '( %s -> %s )' % (B3, UZ('3', 'N')))
n0, zr = zreal(w, B3, c, n3)
v = w.s([c, n0, w.inst('zscaleval')], 'syl2anc', '( %s -> %s = %s )' % (B3, ZS('C', 'N'), NC(ZR('C', 'N'))))
cl = w.s([zr, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (B3, NC(ZR('C', 'N'))))
w.qed([v, cl], 'eqeltrd', '( %s -> %s e. NN0 )' % (B3, ZS('C', 'N'))); run(w)

w = W('zscalege', 'The scale z is at least C * ell2 N * ell3 N (Lean: Nat.le_ceil; DefsW.lean hz_lo).')
c = w.s([], 'simpl', '( %s -> C e. RR )' % B3); n3 = w.s([], 'simpr', '( %s -> %s )' % (B3, UZ('3', 'N')))
n0, zr = zreal(w, B3, c, n3)
v = w.s([c, n0, w.inst('zscaleval')], 'syl2anc', '( %s -> %s = %s )' % (B3, ZS('C', 'N'), NC(ZR('C', 'N'))))
g = w.s([zr, w.inst('nceilge')], 'syl', '( %s -> %s <_ %s )' % (B3, ZR('C', 'N'), NC(ZR('C', 'N'))))
w.qed([g, v], 'breqtrrd', '( %s -> %s <_ %s )' % (B3, ZR('C', 'N'), ZS('C', 'N'))); run(w)

B3p = '( C e. RR /\\ %s /\\ 0 <_ %s )' % (UZ('3', 'N'), ZR('C', 'N'))
w = W('zscalelt', 'The scale z is less than C * ell2 N * ell3 N + 1 when that product is nonnegative (Lean: Nat.ceil_lt_add_one; DefsW.lean hz_hi).')
c = w.s([], 'simp1', '( %s -> C e. RR )' % B3p); n3 = w.s([], 'simp2', '( %s -> %s )' % (B3p, UZ('3', 'N'))); ge = w.s([], 'simp3', '( %s -> 0 <_ %s )' % (B3p, ZR('C', 'N')))
n0, zr = zreal(w, B3p, c, n3)
v = w.s([c, n0, w.inst('zscaleval')], 'syl2anc', '( %s -> %s = %s )' % (B3p, ZS('C', 'N'), NC(ZR('C', 'N'))))
lt = w.s([zr, ge, w.inst('nceillt')], 'syl2anc', '( %s -> %s < ( %s + 1 ) )' % (B3p, NC(ZR('C', 'N')), ZR('C', 'N')))
w.qed([v, lt], 'eqbrtrd', '( %s -> %s < ( %s + 1 ) )' % (B3p, ZS('C', 'N'), ZR('C', 'N'))); run(w)

# ---- yscaleE
w = W('yscaleefval', 'The curried value of yscaleE: the mapping E |-> the natural ceiling of z ^ ( 1 - E ).')
def mptex_steps(w, M):
    r = w.s([], 'reex', 'RR e. _V'); return w.s([r], 'mptex', '%s e. _V' % M)
mpo_val(w, 'df-yscalee', 'yscaleE', YEM, lambda w: mptex_steps(w, YEM('C', 'N'))); qedlast(w); run(w)

def curried_val(label, desc, fvthm, MAP, BODY, VAL, exstep):
    """( A3 -> VAL(C,N,E) = BODY(C,N,E) ) from the mapping value fvthm"""
    w = W(label, desc)
    c = w.s([], 'simp1', '( %s -> C e. RR )' % A3); n = w.s([], 'simp2', '( %s -> N e. NN0 )' % A3); e = w.s([], 'simp3', '( %s -> E e. RR )' % A3)
    f = w.s([c, n, w.inst(fvthm)], 'syl2anc', '( %s -> %s = %s )' % (A3, VAL('C', 'N', 'E')[2:].rsplit(' ` ', 1)[0], MAP('C', 'N')))
    A4 = '( %s /\\ e = E )' % A3
    l1 = w.s([], 'simpr', '( %s -> e = E )' % A4)
    cg, b = w.congr(BODY('C', 'N', 'e'), {'e': 'E'}, A4, {'e': l1}); assert b == BODY('C', 'N', 'E'), b
    x = exstep(w)
    w.qed([f, cg, e, x], 'fvmptd', '( %s -> %s = %s )' % (A3, VAL('C', 'N', 'E'), BODY('C', 'N', 'E'))); run(w)
    return w

curried_val('yscaleeval', 'Value of yscaleE: the natural ceiling of z ^ ( 1 - E ) (Lean: yscaleE).', 'yscaleefval', YEM, YEB, YE,
            lambda w: w.s([w.s([], 'fvex', '%s e. _V' % YEB('C', 'N', 'E'))], 'a1i', '( %s -> %s e. _V )' % (A3, YEB('C', 'N', 'E'))))

def zs_nonneg(w, A, c, n3):
    """( A -> ZS e. RR ), ( A -> 0 <_ ZS ) for N >= 3"""
    z = w.s([c, n3, w.inst('zscalecl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, ZS('C', 'N')))
    return w.s([z], 'nn0red', '( %s -> %s e. RR )' % (A, ZS('C', 'N'))), w.s([z], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A, ZS('C', 'N')))

B3e = '( C e. RR /\\ %s /\\ E e. RR )' % UZ('3', 'N')
w = W('yscaleecl', 'Closure of yscaleE: a nonnegative integer for N >= 3.')
c = w.s([], 'simp1', '( %s -> C e. RR )' % B3e); n3 = w.s([], 'simp2', '( %s -> %s )' % (B3e, UZ('3', 'N'))); e = w.s([], 'simp3', '( %s -> E e. RR )' % B3e)
u2, n0 = n0of3(w, B3e, n3)
v = w.s([c, n0, e, w.inst('yscaleeval')], 'syl3anc', '( %s -> %s = %s )' % (B3e, YE('C', 'N', 'E'), YEB('C', 'N', 'E')))
zr, zge = zs_nonneg(w, B3e, c, n3)
one = w.s([], '1red', '( %s -> 1 e. RR )' % B3e); me = w.s([one, e], 'resubcld', '( %s -> ( 1 - E ) e. RR )' % B3e)
p = w.s([zr, zge, me, w.inst('recxpcl')], 'syl3anc', '( %s -> ( %s ^c ( 1 - E ) ) e. RR )' % (B3e, ZS('C', 'N')))
cl = w.s([p, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (B3e, YEB('C', 'N', 'E')))
w.qed([v, cl], 'eqeltrd', '( %s -> %s e. NN0 )' % (B3e, YE('C', 'N', 'E'))); run(w)

# ---- yscale
w = W('yscaleval', 'Value of yscale: the natural ceiling of z ^ ( 2 / 3 ) (Lean: yscale).')
mpo_val(w, 'df-yscale', 'yscale', YB, lambda w: w.s([], 'fvex', '%s e. _V' % YB('C', 'N'))); qedlast(w); run(w)

w = W('yscalecl', 'Closure of yscale: a nonnegative integer for N >= 3.')
c = w.s([], 'simpl', '( %s -> C e. RR )' % B3); n3 = w.s([], 'simpr', '( %s -> %s )' % (B3, UZ('3', 'N')))
u2, n0 = n0of3(w, B3, n3)
v = w.s([c, n0, w.inst('yscaleval')], 'syl2anc', '( %s -> %s = %s )' % (B3, YS('C', 'N'), YB('C', 'N')))
zr, zge = zs_nonneg(w, B3, c, n3)
r2 = w.s([], '2re', '2 e. RR'); r3 = w.s([], '3re', '3 e. RR'); n3z = w.s([], '3ne0', '3 =/= 0'); q = w.s([r2, r3, n3z], 'redivcli', '( 2 / 3 ) e. RR'); qd = w.s([q], 'a1i', '( %s -> ( 2 / 3 ) e. RR )' % B3)
p = w.s([zr, zge, qd, w.inst('recxpcl')], 'syl3anc', '( %s -> ( %s ^c ( 2 / 3 ) ) e. RR )' % (B3, ZS('C', 'N')))
cl = w.s([p, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (B3, YB('C', 'N')))
w.qed([v, cl], 'eqeltrd', '( %s -> %s e. NN0 )' % (B3, YS('C', 'N'))); run(w)

w = W('yscaleeq', "yscale is yscaleE at E = 1 / 3 (Lean: yscale_eq_yscaleE; the paper's instance).")
c = w.s([], 'simpl', '( %s -> C e. RR )' % A2); n = w.s([], 'simpr', '( %s -> N e. NN0 )' % A2)
v1 = w.s([], 'yscaleval', '( %s -> %s = %s )' % (A2, YS('C', 'N'), YB('C', 'N')))
r1 = w.s([], '1re', '1 e. RR'); r3 = w.s([], '3re', '3 e. RR'); n3z = w.s([], '3ne0', '3 =/= 0'); t = w.s([r1, r3, n3z], 'redivcli', '( 1 / 3 ) e. RR'); td = w.s([t], 'a1i', '( %s -> ( 1 / 3 ) e. RR )' % A2)
v2 = w.s([c, n, td, w.inst('yscaleeval')], 'syl3anc', '( %s -> %s = %s )' % (A2, YE('C', 'N', '( 1 / 3 )'), YEB('C', 'N', '( 1 / 3 )')))
# ( 1 - ( 1 / 3 ) ) = ( 2 / 3 )
c3 = w.s([], '3cn', '3 e. CC'); di = w.s([c3, n3z, w.inst('divid')], 'mp2an', '( 3 / 3 ) = 1'); e1 = w.s([di], 'eqcomi', '1 = ( 3 / 3 )')
o1 = w.s([e1], 'oveq1i', '( 1 - ( 1 / 3 ) ) = ( ( 3 / 3 ) - ( 1 / 3 ) )')
c1 = w.s([], 'ax-1cn', '1 e. CC'); pr = w.s([c3, n3z], 'pm3.2i', '( 3 e. CC /\\ 3 =/= 0 )')
ds = w.s([c3, c1, pr, w.inst('divsubdir')], 'mp3an', '( ( 3 - 1 ) / 3 ) = ( ( 3 / 3 ) - ( 1 / 3 ) )')
m = w.s([], '3m1e2', '( 3 - 1 ) = 2'); o2 = w.s([m], 'oveq1i', '( ( 3 - 1 ) / 3 ) = ( 2 / 3 )')
ds2 = w.s([ds, o2], 'eqtr3i', '( ( 3 / 3 ) - ( 1 / 3 ) ) = ( 2 / 3 )')
eq = w.s([o1, ds2], 'eqtri', '( 1 - ( 1 / 3 ) ) = ( 2 / 3 )')
o3 = w.s([eq], 'oveq2i', '( %s ^c ( 1 - ( 1 / 3 ) ) ) = ( %s ^c ( 2 / 3 ) )' % (ZS('C', 'N'), ZS('C', 'N')))
f3 = w.s([o3], 'fveq2i', '%s = %s' % (YEB('C', 'N', '( 1 / 3 )'), YB('C', 'N'))); f3d = w.s([f3], 'a1i', '( %s -> %s = %s )' % (A2, YEB('C', 'N', '( 1 / 3 )'), YB('C', 'N')))
v2b = w.s([v2, f3d], 'eqtrd', '( %s -> %s = %s )' % (A2, YE('C', 'N', '( 1 / 3 )'), YB('C', 'N')))
w.qed([v1, v2b], 'eqtr4d', '( %s -> %s = %s )' % (A2, YS('C', 'N'), YE('C', 'N', '( 1 / 3 )'))); run(w)

# ---- Tscale
w = W('tscaleval', 'Value of Tscale: the natural ceiling of 3 * ell2 N (Lean: Tscale).')
l1 = w.s([], 'id', '( n = N -> n = N )')
cg, b = w.congr(TB('n'), {'n': 'N'}, 'n = N', {'n': l1}); assert b == TB('N')
d = w.s([], 'df-tscale', 'Tscale = ( n e. NN0 |-> %s )' % TB('n'))
x = w.s([], 'fvex', '%s e. _V' % TB('N'))
w.qed([cg, d, x], 'fvmpt', '( N e. NN0 -> %s = %s )' % (TS('N'), TB('N'))); run(w)

w = W('tscalecl', 'Closure of Tscale: a nonnegative integer for N >= 2.')
A = UZ('2', 'N')
u2 = w.s([], 'id', '( %s -> %s )' % (A, A)); nn = w.s([u2, w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % A); n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A)
v = w.s([n0, w.inst('tscaleval')], 'syl', '( %s -> %s = %s )' % (A, TS('N'), TB('N')))
e2 = w.s([], 'ell2cl', '( %s -> %s e. RR )' % (A, E2('N'))); r3 = w.s([], '3re', '3 e. RR'); r3d = w.s([r3], 'a1i', '( %s -> 3 e. RR )' % A)
m = w.s([r3d, e2], 'remulcld', '( %s -> ( 3 x. %s ) e. RR )' % (A, E2('N')))
cl = w.s([m, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (A, TB('N')))
w.qed([v, cl], 'eqeltrd', '( %s -> %s e. NN0 )' % (A, TS('N'))); run(w)

# ---- goodPrimesE
w = W('goodprimesefval', 'The curried value of goodPrimesE: the mapping E |-> the reservoir.')
mpo_val(w, 'df-goodprimese', 'goodPrimesE', GEM, lambda w: mptex_steps(w, GEM('C', 'N'))); qedlast(w); run(w)

def rabex_steps(w, C, N, Y, A):
    o = w.s([], 'ovex', '( 0 ... %s ) e. _V' % ZS(C, N)); x = w.s([o], 'rabex', '%s e. _V' % RAB(C, N, Y))
    return w.s([x], 'a1i', '( %s -> %s e. _V )' % (A, RAB(C, N, Y)))
curried_val('goodprimeseval', 'Value of goodPrimesE: the primes q in ( z ^ ( 99 / 100 ) , z ] with q - 1 smooth up to yscaleE (Lean: goodPrimesE).', 'goodprimesefval', GEM,
            lambda C, N, E: RAB(C, N, YE(C, N, E)), GE, lambda w: rabex_steps(w, 'C', 'N', YE('C', 'N', 'E'), A3))

def rab_fp(w, C, N, Y, A, valstep, VAL):
    """( A -> VAL e. ( ~P Prime i^i Fin ) ) from valstep: ( A -> VAL = RAB(C,N,Y) )"""
    R = RAB(C, N, Y); D = '( 0 ... %s )' % ZS(C, N)
    inner = R[R.index('| ') + 2:-2]
    s1 = w.s([], 'simp1', '( %s -> q e. Prime )' % inner)
    s1i = w.s([s1], 'a1i', '( q e. %s -> ( %s -> q e. Prime ) )' % (D, inner))
    rg = w.s([s1i], 'rgen', 'A. q e. %s ( %s -> q e. Prime )' % (D, inner))
    ss = w.s([rg, w.inst('rabss')], 'mpbir', '%s C_ Prime' % R)
    fz = w.s([], 'fzfi', '%s e. Fin' % D); fi = w.s([fz, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % R)
    fp = w.s([ss, fi, w.inst('elfpw')], 'mpbir2an', '%s e. ( ~P Prime i^i Fin )' % R)
    fpd = w.s([fp], 'a1i', '( %s -> %s e. ( ~P Prime i^i Fin ) )' % (A, R))
    w.qed([valstep, fpd], 'eqeltrd', '( %s -> %s e. ( ~P Prime i^i Fin ) )' % (A, VAL))

w = W('goodprimesefi', 'The reservoir goodPrimesE is a finite set of primes (Lean: Finset NN, with q.Prime among the filter conditions).')
v = w.s([], 'goodprimeseval', '( %s -> %s = %s )' % (A3, GE('C', 'N', 'E'), RAB('C', 'N', YE('C', 'N', 'E'))))
rab_fp(w, 'C', 'N', YE('C', 'N', 'E'), A3, v, GE('C', 'N', 'E')); run(w)

# ---- goodPrimes
w = W('goodprimesval', 'Value of goodPrimes: the primes q in ( z ^ ( 99 / 100 ) , z ] with q - 1 smooth up to yscale (Lean: goodPrimes).')
mpo_val(w, 'df-goodprimes', 'goodPrimes', lambda c, n: RAB(c, n, YS(c, n)), lambda w: w.s([w.s([], 'ovex', '( 0 ... %s ) e. _V' % ZS('C', 'N'))], 'rabex', '%s e. _V' % RAB('C', 'N', YS('C', 'N')))); qedlast(w); run(w)

w = W('goodprimesfi', 'The reservoir goodPrimes is a finite set of primes.')
v = w.s([], 'goodprimesval', '( %s -> %s = %s )' % (A2, GP('C', 'N'), RAB('C', 'N', YS('C', 'N'))))
rab_fp(w, 'C', 'N', YS('C', 'N'), A2, v, GP('C', 'N')); run(w)

w = W('goodprimeseq', 'goodPrimes is goodPrimesE at E = 1 / 3 (Lean: goodPrimes_eq_goodPrimesE).')
c = w.s([], 'simpl', '( %s -> C e. RR )' % A2); n = w.s([], 'simpr', '( %s -> N e. NN0 )' % A2)
v1 = w.s([], 'goodprimesval', '( %s -> %s = %s )' % (A2, GP('C', 'N'), RAB('C', 'N', YS('C', 'N'))))
r1 = w.s([], '1re', '1 e. RR'); r3 = w.s([], '3re', '3 e. RR'); n3z = w.s([], '3ne0', '3 =/= 0'); t = w.s([r1, r3, n3z], 'redivcli', '( 1 / 3 ) e. RR'); td = w.s([t], 'a1i', '( %s -> ( 1 / 3 ) e. RR )' % A2)
v2 = w.s([c, n, td, w.inst('goodprimeseval')], 'syl3anc', '( %s -> %s = %s )' % (A2, GE('C', 'N', '( 1 / 3 )'), RAB('C', 'N', YE('C', 'N', '( 1 / 3 )'))))
ye = w.s([], 'yscaleeq', '( %s -> %s = %s )' % (A2, YS('C', 'N'), YE('C', 'N', '( 1 / 3 )')))
rw, res = w.rewrite(RAB('C', 'N', YS('C', 'N')), {YS('C', 'N'): (YE('C', 'N', '( 1 / 3 )'), ye)}, A2); assert res == RAB('C', 'N', YE('C', 'N', '( 1 / 3 )')), res
v1b = w.s([v1, rw], 'eqtrd', '( %s -> %s = %s )' % (A2, GP('C', 'N'), res))
w.qed([v1b, v2], 'eqtr4d', '( %s -> %s = %s )' % (A2, GP('C', 'N'), GE('C', 'N', '( 1 / 3 )'))); run(w)
