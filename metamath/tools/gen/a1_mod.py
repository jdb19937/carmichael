"""Sortie A1, batch 4: the modulus Lmod, the search ceiling xceil, lambdaL,
the batch size Nstar and the step 3 prime pool (Defs.lean)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

FP0 = '( ~P NN0 i^i Fin )'
FPP = '( ~P Prime i^i Fin )'
LM = lambda Q: '( Lmod ` %s )' % Q
XC = lambda Q: '( xceil ` %s )' % Q
LAM = lambda Q: '( lambdaL ` %s )' % Q
NST = lambda Q: '( Nstar ` %s )' % Q
PRODQ = lambda Q: 'prod_ q e. %s q' % Q
LAMM = lambda Q: '( q e. %s |-> ( q - 1 ) )' % Q
LAMR = lambda Q: 'ran %s' % LAMM(Q)
LAMB = lambda Q: '( _lcm ` %s )' % LAMR(Q)
XCB = lambda Q: '( %s ^ 5 )' % LM(Q)
NSTX = lambda Q: '( %s x. ( 1 + ( log ` %s ) ) )' % (LAM(Q), LM(Q))
NSTB = lambda Q: '( ( Nceil ` %s ) + 1 )' % NSTX(Q)
DIV = lambda Q: '{ m e. ( 1 ... %s ) | m || %s }' % (LM(Q), LM(Q))
D1 = lambda K: '( ( d x. %s ) + 1 )' % K
COND = lambda Q, Z, K: '( %s <_ %s /\\ %s e. Prime /\\ %s < %s )' % (D1(K), XC(Q), D1(K), Z, D1(K))
PRAB = lambda Q, Z, K: '{ d e. %s | %s }' % (DIV(Q), COND(Q, Z, K))
PMPT = lambda Q, Z, K: '( d e. %s |-> %s )' % (PRAB(Q, Z, K), D1(K))
PBODY = lambda Q, Z, K: 'ran %s' % PMPT(Q, Z, K)
PMAP = lambda Q, Z: '( k e. NN0 |-> %s )' % PBODY(Q, Z, 'k')
PL = lambda Q, Z, K: '( ( %s pool %s ) ` %s )' % (Q, Z, K)

PH0 = 'Q e. %s' % FP0
PHP = 'Q e. %s' % FPP


def fpw(w, ante, phstep, T):
    """( ante -> Q C_ T ), ( ante -> Q e. Fin ) from ( ante -> Q e. ( ~P T i^i Fin ) )"""
    b = w.s([phstep, w.inst('elfpw')], 'sylib', '( %s -> ( Q C_ %s /\\ Q e. Fin ) )' % (ante, T))
    return w.s([b], 'simpld', '( %s -> Q C_ %s )' % (ante, T)), w.s([b], 'simprd', '( %s -> Q e. Fin )' % ante)


def prime_to_nn0(w, ante, sp):
    """( ante -> Q C_ NN0 ) from ( ante -> Q C_ Prime )"""
    a = w.s([], 'prmssnn', 'Prime C_ NN'); b = w.s([], 'nnssnn0', 'NN C_ NN0')
    c = w.s([a, b], 'sstri', 'Prime C_ NN0'); d = w.s([c], 'a1i', '( %s -> Prime C_ NN0 )' % ante)
    return w.s([sp, d], 'sstrd', '( %s -> Q C_ NN0 )' % ante)


def fp0_of_fpp(w, ante, phstep):
    """( ante -> Q e. ( ~P NN0 i^i Fin ) ), Q C_ Prime, Q e. Fin from Q e. ( ~P Prime i^i Fin )"""
    sp, fin = fpw(w, ante, phstep, 'Prime')
    s0 = prime_to_nn0(w, ante, sp)
    j = w.s([s0, fin], 'jca', '( %s -> ( Q C_ NN0 /\\ Q e. Fin ) )' % ante)
    return w.s([j, w.inst('elfpw')], 'sylibr', '( %s -> %s )' % (ante, PH0)), sp, fin


# ---------------------------------------------------------------- Lmod
w = W('lmodqval', 'Value of Lmod: the product of the elements of Q (Lean: Lmod).')
q0 = w.s([], 'id', '( %s -> %s )' % (PH0, PH0))
ss, fin = fpw(w, PH0, q0, 'NN0')
A2 = '( %s /\\ q e. Q )' % PH0
ssd = w.s([ss], 'adantr', '( %s -> Q C_ NN0 )' % A2)
qel = w.s([], 'simpr', '( %s -> q e. Q )' % A2)
ch = w.s([ssd, qel], 'sseldd', '( %s -> q e. NN0 )' % A2)
pc = w.s([fin, ch], 'fprodnn0cl', '( %s -> %s e. NN0 )' % (PH0, PRODQ('Q')))
ex = w.s([pc], 'elexd', '( %s -> %s e. _V )' % (PH0, PRODQ('Q')))
d0 = w.s([], 'df-lmodq', 'Lmod = ( s e. %s |-> %s )' % (FP0, PRODQ('s')))
dfs = w.s([d0], 'a1i', '( %s -> Lmod = ( s e. %s |-> %s ) )' % (PH0, FP0, PRODQ('s')))
A3 = '( %s /\\ s = Q )' % PH0
l1 = w.s([], 'simpr', '( %s -> s = Q )' % A3)
cg, b = w.congr(PRODQ('s'), {'s': 'Q'}, A3, {'s': l1}); assert b == PRODQ('Q'), b
w.qed([dfs, cg, q0, ex], 'fvmptd', '( %s -> %s = %s )' % (PH0, LM('Q'), PRODQ('Q')))
run(w)

w = W('lmodqcl', 'Closure of Lmod: a positive integer when Q is a finite set of primes.')
qp = w.s([], 'id', '( %s -> %s )' % (PHP, PHP))
f0, sp, fin = fp0_of_fpp(w, PHP, qp)
v = w.s([f0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (PHP, LM('Q'), PRODQ('Q')))
B2 = '( %s /\\ q e. Q )' % PHP
spd = w.s([sp], 'adantr', '( %s -> Q C_ Prime )' % B2)
qel = w.s([], 'simpr', '( %s -> q e. Q )' % B2)
qpr = w.s([spd, qel], 'sseldd', '( %s -> q e. Prime )' % B2)
qnn = w.s([qpr, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % B2)
pc = w.s([fin, qnn], 'fprodnncl', '( %s -> %s e. NN )' % (PHP, PRODQ('Q')))
w.qed([v, pc], 'eqeltrd', '( %s -> %s e. NN )' % (PHP, LM('Q')))
run(w)

# ---------------------------------------------------------------- xceil
w = W('xceilval', 'Value of xceil: the fifth power of the modulus (Lean: xceil).')
l1 = w.s([], 'id', '( s = Q -> s = Q )')
cg, b = w.congr(XCB('s'), {'s': 'Q'}, 's = Q', {'s': l1}); assert b == XCB('Q'), b
d0 = w.s([], 'df-xceil', 'xceil = ( s e. %s |-> %s )' % (FP0, XCB('s')))
x0 = w.s([], 'ovex', '%s e. _V' % XCB('Q'))
w.qed([cg, d0, x0], 'fvmpt', '( %s -> %s = %s )' % (PH0, XC('Q'), XCB('Q')))
run(w)

w = W('xceilcl', 'Closure of xceil: a positive integer when Q is a finite set of primes.')
qp = w.s([], 'id', '( %s -> %s )' % (PHP, PHP))
f0, sp, fin = fp0_of_fpp(w, PHP, qp)
v = w.s([f0, w.inst('xceilval')], 'syl', '( %s -> %s = %s )' % (PHP, XC('Q'), XCB('Q')))
lc = w.s([], 'lmodqcl', '( %s -> %s e. NN )' % (PHP, LM('Q')))
n5 = w.s([], '5nn0', '5 e. NN0'); n5d = w.s([n5], 'a1i', '( %s -> 5 e. NN0 )' % PHP)
pc = w.s([lc, n5d, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (PHP, XCB('Q')))
w.qed([v, pc], 'eqeltrd', '( %s -> %s e. NN )' % (PHP, XC('Q')))
run(w)

# ---------------------------------------------------------------- lambdaL
w = W('lambdalval', 'Value of lambdaL: the least common multiple of the q - 1 (Lean: lambdaL).')
l1 = w.s([], 'id', '( s = Q -> s = Q )')
cg, b = w.congr(LAMB('s'), {'s': 'Q'}, 's = Q', {'s': l1}); assert b == LAMB('Q'), b
d0 = w.s([], 'df-lambdal', 'lambdaL = ( s e. %s |-> %s )' % (FP0, LAMB('s')))
x0 = w.s([], 'fvex', '%s e. _V' % LAMB('Q'))
w.qed([cg, d0, x0], 'fvmpt', '( %s -> %s = %s )' % (PH0, LAM('Q'), LAMB('Q')))
run(w)


def lamrange(w, ante, sp, fin):
    """( ante -> ran ( q e. Q |-> ( q - 1 ) ) C_ NN ) and ( ... e. Fin )"""
    B2 = '( %s /\\ q e. Q )' % ante
    spd = w.s([sp], 'adantr', '( %s -> Q C_ Prime )' % B2)
    qel = w.s([], 'simpr', '( %s -> q e. Q )' % B2)
    qpr = w.s([spd, qel], 'sseldd', '( %s -> q e. Prime )' % B2)
    u2 = w.s([qpr, w.inst('prmuz2')], 'syl', '( %s -> q e. ( ZZ>= ` 2 ) )' % B2)
    m1 = w.s([u2, w.inst('uz2m1nn')], 'syl', '( %s -> ( q - 1 ) e. NN )' % B2)
    ral = w.s([m1], 'ralrimiva', '( %s -> A. q e. Q ( q - 1 ) e. NN )' % ante)
    eq = w.s([], 'eqid', '%s = %s' % (LAMM('Q'), LAMM('Q')))
    i = w.s([eq], 'rnmptss', '( A. q e. Q ( q - 1 ) e. NN -> %s C_ NN )' % LAMR('Q'))
    ss = w.s([ral, i], 'syl', '( %s -> %s C_ NN )' % (ante, LAMR('Q')))
    mf = w.s([fin, w.inst('mptfi')], 'syl', '( %s -> %s e. Fin )' % (ante, LAMM('Q')))
    rf = w.s([mf, w.inst('rnfi')], 'syl', '( %s -> %s e. Fin )' % (ante, LAMR('Q')))
    return ss, rf


w = W('lambdalcl', 'Closure of lambdaL: a positive integer when Q is a finite set of primes.')
qp = w.s([], 'id', '( %s -> %s )' % (PHP, PHP))
f0, sp, fin = fp0_of_fpp(w, PHP, qp)
v = w.s([f0, w.inst('lambdalval')], 'syl', '( %s -> %s = %s )' % (PHP, LAM('Q'), LAMB('Q')))
ss, rf = lamrange(w, PHP, sp, fin)
lc = w.s([ss, rf, w.inst('lcmfnncl')], 'syl2anc', '( %s -> %s e. NN )' % (PHP, LAMB('Q')))
w.qed([v, lc], 'eqeltrd', '( %s -> %s e. NN )' % (PHP, LAM('Q')))
run(w)


PHPP = '( %s /\\ P e. Q )' % PHP
w = W('lambdaldvds', 'Each q - 1 for q in Q divides lambdaL Q (Lean: Finset.dvd_lcm; Extraction.lean).')
qp = w.s([], 'simpl', '( %s -> %s )' % (PHPP, PHP))
pel = w.s([], 'simpr', '( %s -> P e. Q )' % PHPP)
f0, sp, fin = fp0_of_fpp(w, PHPP, qp)
v = w.s([f0, w.inst('lambdalval')], 'syl', '( %s -> %s = %s )' % (PHPP, LAM('Q'), LAMB('Q')))
ss, rf = lamrange(w, PHPP, sp, fin)
zss = w.s([], 'nnssz', 'NN C_ ZZ'); zssd = w.s([zss], 'a1i', '( %s -> NN C_ ZZ )' % PHPP)
ssz = w.s([ss, zssd], 'sstrd', '( %s -> %s C_ ZZ )' % (PHPP, LAMR('Q')))
dv = w.s([ssz, rf, w.inst('dvdslcmf')], 'syl2anc', '( %s -> A. x e. %s x || %s )' % (PHPP, LAMR('Q'), LAMB('Q')))
ppr = w.s([sp, pel], 'sseldd', '( %s -> P e. Prime )' % PHPP)
pu2 = w.s([ppr, w.inst('prmuz2')], 'syl', '( %s -> P e. ( ZZ>= ` 2 ) )' % PHPP)
pm1 = w.s([pu2, w.inst('uz2m1nn')], 'syl', '( %s -> ( P - 1 ) e. NN )' % PHPP)
pex = w.s([pm1], 'elexd', '( %s -> ( P - 1 ) e. _V )' % PHPP)
eq = w.s([], 'eqid', '%s = %s' % (LAMM('Q'), LAMM('Q')))
A4 = '( %s /\\ q = P )' % PHPP
lq = w.s([], 'simpr', '( %s -> q = P )' % A4)
cgp, bb = w.congr('( q - 1 )', {'q': 'P'}, A4, {'q': lq}); assert bb == '( P - 1 )', bb
cgr = w.s([cgp], 'eqcomd', '( %s -> ( P - 1 ) = ( q - 1 ) )' % A4)
mem = w.s([eq, pel, pex, cgr], 'elrnmptdv', '( %s -> ( P - 1 ) e. %s )' % (PHPP, LAMR('Q')))
idx = w.s([], 'id', '( x = ( P - 1 ) -> x = ( P - 1 ) )')
cgw, bw = w.wcongr('x || %s' % LAMB('Q'), {'x': '( P - 1 )'}, 'x = ( P - 1 )', {'x': idx})
assert bw == '( P - 1 ) || %s' % LAMB('Q'), bw
r = w.s([cgw, dv, mem], 'rspcdva', '( %s -> ( P - 1 ) || %s )' % (PHPP, LAMB('Q')))
w.qed([r, v], 'breqtrrd', '( %s -> ( P - 1 ) || %s )' % (PHPP, LAM('Q')))
run(w)

# ---------------------------------------------------------------- Nstar
w = W('nstarval', 'Value of Nstar: the natural ceiling of lambdaL Q * ( 1 + log ( Lmod Q ) ) plus one (Lean: Nstar).')
l1 = w.s([], 'id', '( s = Q -> s = Q )')
cg, b = w.congr(NSTB('s'), {'s': 'Q'}, 's = Q', {'s': l1}); assert b == NSTB('Q'), b
d0 = w.s([], 'df-nstar', 'Nstar = ( s e. %s |-> %s )' % (FP0, NSTB('s')))
x0 = w.s([], 'ovex', '%s e. _V' % NSTB('Q'))
w.qed([cg, d0, x0], 'fvmpt', '( %s -> %s = %s )' % (PH0, NST('Q'), NSTB('Q')))
run(w)

w = W('nstarcl', 'Closure of Nstar: a positive integer when Q is a finite set of primes.')
qp = w.s([], 'id', '( %s -> %s )' % (PHP, PHP))
f0, sp, fin = fp0_of_fpp(w, PHP, qp)
v = w.s([f0, w.inst('nstarval')], 'syl', '( %s -> %s = %s )' % (PHP, NST('Q'), NSTB('Q')))
lam = w.s([], 'lambdalcl', '( %s -> %s e. NN )' % (PHP, LAM('Q')))
lamr = w.s([lam], 'nnred', '( %s -> %s e. RR )' % (PHP, LAM('Q')))
lmod = w.s([], 'lmodqcl', '( %s -> %s e. NN )' % (PHP, LM('Q')))
lrp = w.s([lmod], 'nnrpd', '( %s -> %s e. RR+ )' % (PHP, LM('Q')))
lg = w.s([lrp], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (PHP, LM('Q')))
one = w.s([], '1red', '( %s -> 1 e. RR )' % PHP)
s1 = w.s([one, lg], 'readdcld', '( %s -> ( 1 + ( log ` %s ) ) e. RR )' % (PHP, LM('Q')))
pr = w.s([lamr, s1], 'remulcld', '( %s -> %s e. RR )' % (PHP, NSTX('Q')))
nc = w.s([pr, w.inst('nceilcl')], 'syl', '( %s -> ( Nceil ` %s ) e. NN0 )' % (PHP, NSTX('Q')))
p1 = w.s([nc, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (PHP, NSTB('Q')))
w.qed([v, p1], 'eqeltrd', '( %s -> %s e. NN )' % (PHP, NST('Q')))
run(w)

# ---------------------------------------------------------------- pool
A3P = '( %s /\\ Z e. NN0 /\\ K e. NN0 )' % PH0
A2P = '( %s /\\ Z e. NN0 )' % PH0
PS = 'P = %s' % D1('K')
RHS = 'E. d e. %s ( %s /\\ %s )' % (DIV('Q'), COND('Q', 'Z', 'K'), PS)


def mptcong(w, ante, dom_old, dom_new, body_old, body_new, dstep, bstep):
    """( ante -> ( d e. dom_old |-> body_old ) = ( d e. dom_new |-> body_new ) ),
    by mpteq12df / mpteq1df: the mpt domain mentions the bound variable d, so the
    lemmas with $d d A are unusable."""
    old = '( d e. %s |-> %s )' % (dom_old, body_old)
    new = '( d e. %s |-> %s )' % (dom_new, body_new)
    f = '( %s -> %s = %s )' % (ante, old, new)
    nf = w.s([], 'nfv', 'F/ d %s' % ante)
    if dstep and bstep:
        return w.s([nf, dstep, bstep], 'mpteq12df', f)
    if dstep:
        return w.s([nf, dstep], 'mpteq1df', f)
    return w.s([bstep], 'mpteq2dv', f)


def poolfinite(w, Q, Z, K):
    """closed steps: ( ran ( d e. PRAB |-> D1 ) e. _V , ... e. Fin )"""
    fz = w.s([], 'fzfi', '( 1 ... %s ) e. Fin' % LM(Q))
    dvf = w.s([fz, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % DIV(Q))
    rbf = w.s([dvf, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % PRAB(Q, Z, K))
    rbv = w.s([rbf], 'elexi', '%s e. _V' % PRAB(Q, Z, K))
    nf = w.s([], 'nfrab1', 'F/_ d %s' % PRAB(Q, Z, K))
    mex = w.s([nf, rbv], 'mptexf', '%s e. _V' % PMPT(Q, Z, K))
    rex = w.s([mex], 'rnex', '%s e. _V' % PBODY(Q, Z, K))
    fun = w.s([], 'funmpt', 'Fun %s' % PMPT(Q, Z, K))
    fn = w.s([fun, w.inst('funfn')], 'mpbi', '%s Fn dom %s' % (PMPT(Q, Z, K), PMPT(Q, Z, K)))
    eq = w.s([], 'eqid', '%s = %s' % (PMPT(Q, Z, K), PMPT(Q, Z, K)))
    DR = '{ d e. %s | %s e. _V }' % (PRAB(Q, Z, K), D1(K))
    dm = w.s([eq], 'dmmpt', 'dom %s = %s' % (PMPT(Q, Z, K), DR))
    ss = w.s([nf], 'ssrab2f', '%s C_ %s' % (DR, PRAB(Q, Z, K)))
    sf = w.s([rbf, ss, w.inst('ssfi')], 'mp2an', '%s e. Fin' % DR)
    dmf = w.s([dm, sf], 'eqeltri', 'dom %s e. Fin' % PMPT(Q, Z, K))
    mf = w.s([fn, dmf, w.inst('fnfi')], 'mp2an', '%s e. Fin' % PMPT(Q, Z, K))
    bf = w.s([mf, w.inst('rnfi')], 'ax-mp', '%s e. Fin' % PBODY(Q, Z, K))
    return rex, bf


w = W('poolfval', 'The curried value of pool: the mapping k |-> the pool of primes d * k + 1.')
A = '( s = Q /\\ z = Z )'
l1 = w.s([], 'simpl', '( %s -> s = Q )' % A); l2 = w.s([], 'simpr', '( %s -> z = Z )' % A)
cgd, bd = w.congr(PRAB('s', 'z', 'k'), {'s': 'Q', 'z': 'Z'}, A, {'s': l1, 'z': l2})
assert bd == PRAB('Q', 'Z', 'k'), bd
cgm = mptcong(w, A, PRAB('s', 'z', 'k'), PRAB('Q', 'Z', 'k'), D1('k'), D1('k'), cgd, None)
cg, b = w.congr(PMAP('s', 'z'), {'s': 'Q', 'z': 'Z'}, A, {'s': l1, 'z': l2},
                rules={PMPT('s', 'z', 'k'): (PMPT('Q', 'Z', 'k'), cgm)})
assert b == PMAP('Q', 'Z'), b
d0 = w.s([], 'df-pool', 'pool = ( s e. %s , z e. NN0 |-> %s )' % (FP0, PMAP('s', 'z')))
r = w.s([], 'nn0ex', 'NN0 e. _V'); x0 = w.s([r], 'mptex', '%s e. _V' % PMAP('Q', 'Z'))
w.qed([cg, d0, x0], 'ovmpoa', '( %s -> ( Q pool Z ) = %s )' % (A2P, PMAP('Q', 'Z')))
run(w)

w = W('poolval', 'Value of pool: the primes d * K + 1 at most xceil Q and above Z, for d a divisor of the modulus (Lean: pool).')
q0 = w.s([], 'simp1', '( %s -> %s )' % (A3P, PH0))
z0 = w.s([], 'simp2', '( %s -> Z e. NN0 )' % A3P)
k0 = w.s([], 'simp3', '( %s -> K e. NN0 )' % A3P)
f = w.s([q0, z0, w.inst('poolfval')], 'syl2anc', '( %s -> ( Q pool Z ) = %s )' % (A3P, PMAP('Q', 'Z')))
A4 = '( %s /\\ k = K )' % A3P
l1 = w.s([], 'simpr', '( %s -> k = K )' % A4)
cgd, bd = w.congr(PRAB('Q', 'Z', 'k'), {'k': 'K'}, A4, {'k': l1}); assert bd == PRAB('Q', 'Z', 'K'), bd
cgb, bb = w.congr(D1('k'), {'k': 'K'}, A4, {'k': l1}); assert bb == D1('K'), bb
cgm = mptcong(w, A4, PRAB('Q', 'Z', 'k'), PRAB('Q', 'Z', 'K'), D1('k'), D1('K'), cgd, cgb)
cg = w.s([cgm], 'rneqd', '( %s -> %s = %s )' % (A4, PBODY('Q', 'Z', 'k'), PBODY('Q', 'Z', 'K')))
rex, bfin = poolfinite(w, 'Q', 'Z', 'K')
rxd = w.s([rex], 'a1i', '( %s -> %s e. _V )' % (A3P, PBODY('Q', 'Z', 'K')))
w.qed([f, cg, k0, rxd], 'fvmptd', '( %s -> %s = %s )' % (A3P, PL('Q', 'Z', 'K'), PBODY('Q', 'Z', 'K')))
run(w)

w = W('poolfi', 'The pool is a finite set.')
v = w.s([], 'poolval', '( %s -> %s = %s )' % (A3P, PL('Q', 'Z', 'K'), PBODY('Q', 'Z', 'K')))
rex, bfin = poolfinite(w, 'Q', 'Z', 'K')
rfd = w.s([bfin], 'a1i', '( %s -> %s e. Fin )' % (A3P, PBODY('Q', 'Z', 'K')))
w.qed([v, rfd], 'eqeltrd', '( %s -> %s e. Fin )' % (A3P, PL('Q', 'Z', 'K')))
run(w)

w = W('elpool', 'Membership in the pool: P is d * K + 1 for a divisor d of the modulus meeting the three conditions (Lean: Finset.mem_image, Finset.mem_filter).')
v = w.s([], 'poolval', '( %s -> %s = %s )' % (A3P, PL('Q', 'Z', 'K'), PBODY('Q', 'Z', 'K')))
e1 = w.s([v], 'eleq2d', '( %s -> ( P e. %s <-> P e. %s ) )' % (A3P, PL('Q', 'Z', 'K'), PBODY('Q', 'Z', 'K')))
ov = w.s([], 'ovex', '%s e. _V' % D1('K'))
rg = w.s([ov], 'rgenw', 'A. d e. %s %s e. _V' % (PRAB('Q', 'Z', 'K'), D1('K')))
eq = w.s([], 'eqid', '%s = %s' % (PMPT('Q', 'Z', 'K'), PMPT('Q', 'Z', 'K')))
i = w.s([eq], 'elrnmptg', '( A. d e. %s %s e. _V -> ( P e. %s <-> E. d e. %s %s ) )'
        % (PRAB('Q', 'Z', 'K'), D1('K'), PBODY('Q', 'Z', 'K'), PRAB('Q', 'Z', 'K'), PS))
e2 = w.s([rg, i], 'ax-mp', '( P e. %s <-> E. d e. %s %s )' % (PBODY('Q', 'Z', 'K'), PRAB('Q', 'Z', 'K'), PS))
r1 = w.s([], 'df-rex', '( E. d e. %s %s <-> E. d ( d e. %s /\\ %s ) )' % (PRAB('Q', 'Z', 'K'), PS, PRAB('Q', 'Z', 'K'), PS))
r2 = w.s([], 'rabid', '( d e. %s <-> ( d e. %s /\\ %s ) )' % (PRAB('Q', 'Z', 'K'), DIV('Q'), COND('Q', 'Z', 'K')))
r3 = w.s([r2], 'anbi1i', '( ( d e. %s /\\ %s ) <-> ( ( d e. %s /\\ %s ) /\\ %s ) )' % (PRAB('Q', 'Z', 'K'), PS, DIV('Q'), COND('Q', 'Z', 'K'), PS))
r4 = w.s([], 'anass', '( ( ( d e. %s /\\ %s ) /\\ %s ) <-> ( d e. %s /\\ ( %s /\\ %s ) ) )' % (DIV('Q'), COND('Q', 'Z', 'K'), PS, DIV('Q'), COND('Q', 'Z', 'K'), PS))
r5 = w.s([r3, r4], 'bitri', '( ( d e. %s /\\ %s ) <-> ( d e. %s /\\ ( %s /\\ %s ) ) )' % (PRAB('Q', 'Z', 'K'), PS, DIV('Q'), COND('Q', 'Z', 'K'), PS))
r6 = w.s([r5], 'exbii', '( E. d ( d e. %s /\\ %s ) <-> E. d ( d e. %s /\\ ( %s /\\ %s ) ) )' % (PRAB('Q', 'Z', 'K'), PS, DIV('Q'), COND('Q', 'Z', 'K'), PS))
r7 = w.s([], 'df-rex', '( %s <-> E. d ( d e. %s /\\ ( %s /\\ %s ) ) )' % (RHS, DIV('Q'), COND('Q', 'Z', 'K'), PS))
r8 = w.s([r1, r6], 'bitri', '( E. d e. %s %s <-> E. d ( d e. %s /\\ ( %s /\\ %s ) ) )' % (PRAB('Q', 'Z', 'K'), PS, DIV('Q'), COND('Q', 'Z', 'K'), PS))
r9 = w.s([r8, r7], 'bitr4i', '( E. d e. %s %s <-> %s )' % (PRAB('Q', 'Z', 'K'), PS, RHS))
e3 = w.s([e2, r9], 'bitri', '( P e. %s <-> %s )' % (PBODY('Q', 'Z', 'K'), RHS))
e3d = w.s([e3], 'a1i', '( %s -> ( P e. %s <-> %s ) )' % (A3P, PBODY('Q', 'Z', 'K'), RHS))
w.qed([e1, e3d], 'bitrd', '( %s -> ( P e. %s <-> %s ) )' % (A3P, PL('Q', 'Z', 'K'), RHS))
run(w)

GOAL = '( P e. Prime /\\ Z < P /\\ P <_ %s )' % XC('Q')
w = W('poolel', 'The elements of the pool are primes above Z and at most xceil Q.')
ANT = '( %s /\\ P e. %s )' % (A3P, PL('Q', 'Z', 'K'))
ep = w.s([], 'elpool', '( %s -> ( P e. %s <-> %s ) )' % (A3P, PL('Q', 'Z', 'K'), RHS))
IN = '( ( %s /\\ d e. %s ) /\\ ( %s /\\ %s ) )' % (A3P, DIV('Q'), COND('Q', 'Z', 'K'), PS)
cd = w.s([], 'simprl', '( %s -> %s )' % (IN, COND('Q', 'Z', 'K')))
pe = w.s([], 'simprr', '( %s -> %s )' % (IN, PS))
c1 = w.s([cd], 'simp1d', '( %s -> %s <_ %s )' % (IN, D1('K'), XC('Q')))
c2 = w.s([cd], 'simp2d', '( %s -> %s e. Prime )' % (IN, D1('K')))
c3 = w.s([cd], 'simp3d', '( %s -> Z < %s )' % (IN, D1('K')))
g1 = w.s([pe, c2], 'eqeltrd', '( %s -> P e. Prime )' % IN)
g2 = w.s([c3, pe], 'breqtrrd', '( %s -> Z < P )' % IN)
g3 = w.s([pe, c1], 'eqbrtrd', '( %s -> P <_ %s )' % (IN, XC('Q')))
g = w.s([g1, g2, g3], '3jca', '( %s -> %s )' % (IN, GOAL))
gx = w.s([g], 'ex', '( ( %s /\\ d e. %s ) -> ( ( %s /\\ %s ) -> %s ) )' % (A3P, DIV('Q'), COND('Q', 'Z', 'K'), PS, GOAL))
rl = w.s([gx], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (A3P, RHS, GOAL))
sb = w.s([ep, rl], 'sylbid', '( %s -> ( P e. %s -> %s ) )' % (A3P, PL('Q', 'Z', 'K'), GOAL))
w.qed([sb], 'imp', '( %s -> %s )' % (ANT, GOAL))
run(w)

w = W('poolss', 'The pool is a set of primes.')
A5 = '( %s /\\ x e. %s )' % (A3P, PL('Q', 'Z', 'K'))
pl = w.s([], 'poolel', '( %s -> ( x e. Prime /\\ Z < x /\\ x <_ %s ) )' % (A5, XC('Q')))
p1 = w.s([pl], 'simp1d', '( %s -> x e. Prime )' % A5)
px = w.s([p1], 'ex', '( %s -> ( x e. %s -> x e. Prime ) )' % (A3P, PL('Q', 'Z', 'K')))
w.qed([px], 'ssrdv', '( %s -> %s C_ Prime )' % (A3P, PL('Q', 'Z', 'K')))
run(w)
