"""Sortie C0, batch 5: the affine reparametrisation of a directed integral
(iblcnunit, iooirev, ditgafflem1-4, ditgaff)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w, h=False):
    if only and w.label not in only: return True
    return runh(w) if h else w.run()

HCN = 'H e. ( ( 0 [,] 1 ) -cn-> CC )'
A3 = '( %s /\\ P e. ( 0 [,] 1 ) /\\ Q e. ( 0 [,] 1 ) )' % HCN
AR = 'A. r e. ( 0 (,) 1 ) ( P + ( r x. ( Q - P ) ) ) e. ( 0 (,) 1 )'
PHA = '( %s /\\ %s )' % (A3, AR)
def LN(x): return '( P + ( %s x. ( Q - P ) ) )' % x
def HB(x): return '( ( H ` %s ) x. ( Q - P ) )' % LN(x)
HC = '( w e. ( 0 [,] 1 ) |-> %s )' % HB('w')
GDEF = '( u e. ( 0 [,] 1 ) |-> S. ( 0 (,) u ) ( H ` s ) _d s )'
KDEF = '( u e. ( 0 [,] 1 ) |-> S. ( 0 (,) u ) ( %s ` s ) _d s )' % HC


def linsub(w, frm, to):
    """closed step ( frm = to -> LN ( frm ) = LN ( to ) )"""
    e = w.s([], 'oveq1', '( %s = %s -> ( %s x. ( Q - P ) ) = ( %s x. ( Q - P ) ) )' % (frm, to, frm, to))
    return w.s([e], 'oveq2d', '( %s = %s -> %s = %s )' % (frm, to, LN(frm), LN(to)))


def hbsub(w, frm, to):
    """closed step ( frm = to -> HB ( frm ) = HB ( to ) )"""
    l = linsub(w, frm, to)
    f = w.s([l], 'fveq2d', '( %s = %s -> ( H ` %s ) = ( H ` %s ) )' % (frm, to, LN(frm), LN(to)))
    return w.s([f], 'oveq1d', '( %s = %s -> %s = %s )' % (frm, to, HB(frm), HB(to)))


def hcval(w, x):
    """closed step ( x e. ( 0 [,] 1 ) -> ( HC ` x ) = HB ( x ) )"""
    s = hbsub(w, 'w', x)
    e = w.s([], 'eqid', '%s = %s' % (HC, HC))
    v = w.s([], 'ovex', '%s e. _V' % HB(x))
    return w.s([s, e, v], 'fvmpt', '( %s e. ( 0 [,] 1 ) -> ( %s ` %s ) = %s )' % (x, HC, x, HB(x)))


def iblsteps(w, ante, Fn, hcnstep, v, name=None):
    """( ante -> ( v e. ( 0 (,) 1 ) |-> ( Fn ` v ) ) e. L^1 ) from hcnstep proving
    ( ante -> Fn e. ( ( 0 [,] 1 ) -cn-> CC ) )"""
    ff = w.s([hcnstep, w.inst('cncff')], 'syl', '( %s -> %s : ( 0 [,] 1 ) --> CC )' % (ante, Fn))
    r0 = w.s([], '0red', '( %s -> 0 e. RR )' % ante); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % ante)
    ib = w.s([r0, r1, hcnstep, w.inst('cniccibl')], 'syl3anc', '( %s -> %s e. L^1 )' % (ante, Fn))
    hm = w.s([ff], 'feqmptd', '( %s -> %s = ( %s e. ( 0 [,] 1 ) |-> ( %s ` %s ) ) )' % (ante, Fn, v, Fn, v))
    ibi = w.s([hm, ib], 'eqeltrrd', '( %s -> ( %s e. ( 0 [,] 1 ) |-> ( %s ` %s ) ) e. L^1 )' % (ante, v, Fn, v))
    ss = closed(w, ante, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
    mb = closed(w, ante, 'ioombl', '( 0 (,) 1 ) e. dom vol')
    A2 = '( %s /\\ %s e. ( 0 [,] 1 ) )' % (ante, v)
    ff2 = w.s([ff], 'adantr', '( %s -> %s : ( 0 [,] 1 ) --> CC )' % (A2, Fn))
    vv = w.s([], 'simpr', '( %s -> %s e. ( 0 [,] 1 ) )' % (A2, v))
    fv = w.s([ff2, vv], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (A2, Fn, v))
    return w.s([ss, mb, fv, ibi], 'iblss', '( %s -> ( %s e. ( 0 (,) 1 ) |-> ( %s ` %s ) ) e. L^1 )' % (ante, v, Fn, v), name=name)


# ---- iblcnunit
w = W('iblcnunit', 'A function continuous on the closed unit interval is integrable on the open unit interval.')
h = w.s([], 'id', '( %s -> %s )' % (HCN, HCN))
iblsteps(w, HCN, 'H', h, 's', name='qed')
run(w)

# ---- iooirev
w = W('iooirev', 'The reversal of a point of the open unit interval lies in the open unit interval.')
A = 'T e. ( 0 (,) 1 )'
h = w.s([], 'id', '( %s -> %s )' % (A, A))
tr = w.s([h, w.inst('elioore')], 'syl', '( %s -> T e. RR )' % A)
ord = w.s([h, w.inst('eliooord')], 'syl', '( %s -> ( 0 < T /\\ T < 1 ) )' % A)
lo = w.s([ord], 'simpld', '( %s -> 0 < T )' % A); hi = w.s([ord], 'simprd', '( %s -> T < 1 )' % A)
r1 = w.s([], '1red', '( %s -> 1 e. RR )' % A)
sub = w.s([r1, tr], 'resubcld', '( %s -> ( 1 - T ) e. RR )' % A)
pd = w.s([tr, r1], 'posdifd', '( %s -> ( T < 1 <-> 0 < ( 1 - T ) ) )' % A)
g0 = w.s([hi, pd], 'mpbid', '( %s -> 0 < ( 1 - T ) )' % A)
lp = w.s([tr, r1, w.inst('ltaddpos')], 'syl2anc', '( %s -> ( 0 < T <-> 1 < ( 1 + T ) ) )' % A)
l1a = w.s([lo, lp], 'mpbid', '( %s -> 1 < ( 1 + T ) )' % A)
la = w.s([r1, tr, r1, w.inst('ltsubadd')], 'syl3anc', '( %s -> ( ( 1 - T ) < 1 <-> 1 < ( 1 + T ) ) )' % A)
l1 = w.s([l1a, la], 'mpbird', '( %s -> ( 1 - T ) < 1 )' % A)
x0 = closed(w, A, '0xr', '0 e. RR*'); x1 = closed(w, A, '1xr', '1 e. RR*')
b = w.s([x0, x1, w.inst('elioo2')], 'syl2anc', '( %s -> ( ( 1 - T ) e. ( 0 (,) 1 ) <-> ( ( 1 - T ) e. RR /\\ 0 < ( 1 - T ) /\\ ( 1 - T ) < 1 ) ) )' % A)
w.qed([sub, g0, l1, b], 'mpbir3and', '( %s -> ( 1 - T ) e. ( 0 (,) 1 ) )' % A); run(w)

# ---- ditgafflem1
w = W('ditgafflem1', 'The integrand of the affinely reparametrised integral is continuous on the closed unit interval.')
hcn = w.s([], 'simp1', '( %s -> %s )' % (A3, HCN))
p01 = w.s([], 'simp2', '( %s -> P e. ( 0 [,] 1 ) )' % A3); q01 = w.s([], 'simp3', '( %s -> Q e. ( 0 [,] 1 ) )' % A3)
pc = w.s([p01, w.inst('elunitcn')], 'syl', '( %s -> P e. CC )' % A3)
qc = w.s([q01, w.inst('elunitcn')], 'syl', '( %s -> Q e. CC )' % A3)
r0 = w.s([], '0red', '( %s -> 0 e. RR )' % A3); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % A3)
j1 = w.s([r0, r1], 'jca', '( %s -> ( 0 e. RR /\\ 1 e. RR ) )' % A3)
j2 = w.s([p01, q01], 'jca', '( %s -> ( P e. ( 0 [,] 1 ) /\\ Q e. ( 0 [,] 1 ) ) )' % A3)
seg = w.s([j1, j2, w.inst('csegicc')], 'syl2anc', '( %s -> ( P cseg Q ) C_ ( 0 [,] 1 ) )' % A3)
pq = w.s([pc, qc], 'jca', '( %s -> ( P e. CC /\\ Q e. CC ) )' % A3)
hs = w.s([hcn, seg], 'jca', '( %s -> ( %s /\\ ( P cseg Q ) C_ ( 0 [,] 1 ) ) )' % (A3, HCN))
si = w.s([], 'ssidd', '( %s -> ( 0 [,] 1 ) C_ ( 0 [,] 1 ) )' % A3)
cn = w.s([pq, hs, si, w.inst('lintcnlem')], 'syl3anc', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (A3, HB('t')))
sb = hbsub(w, 't', 'w')
cb = w.s([sb], 'cbvmptv', '( t e. ( 0 [,] 1 ) |-> %s ) = %s' % (HB('t'), HC))
cbd = w.s([cb], 'a1i', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) = %s )' % (A3, HB('t'), HC))
w.qed([cbd, cn], 'eqeltrrd', '( %s -> %s e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (A3, HC)); run(w)

# ---- ditgafflem2
w = W('ditgafflem2', 'The chain rule for the indefinite integral composed with an affine map of the open unit interval into itself.')
w.s([], 'ditgafflem2.g', 'G = %s' % GDEF, name='h1')
hcn = w.s([], 'simpl1', '( %s -> %s )' % (PHA, HCN))
p01 = w.s([], 'simpl2', '( %s -> P e. ( 0 [,] 1 ) )' % PHA); q01 = w.s([], 'simpl3', '( %s -> Q e. ( 0 [,] 1 ) )' % PHA)
ar = w.s([], 'simpr', '( %s -> %s )' % (PHA, AR))
pc = w.s([p01, w.inst('elunitcn')], 'syl', '( %s -> P e. CC )' % PHA)
qc = w.s([q01, w.inst('elunitcn')], 'syl', '( %s -> Q e. CC )' % PHA)
g0 = w.s(['1'], 'ftc1icccn', '( %s -> G e. ( ( 0 [,] 1 ) -cn-> CC ) )' % HCN)
gcn = w.s([hcn, g0], 'syl', '( %s -> G e. ( ( 0 [,] 1 ) -cn-> CC ) )' % PHA)
gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : ( 0 [,] 1 ) --> CC )' % PHA)
hf = w.s([hcn, w.inst('cncff')], 'syl', '( %s -> H : ( 0 [,] 1 ) --> CC )' % PHA)
rr = closed(w, PHA, 'reelprrecn', 'RR e. { RR , CC }')
AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % PHA
to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AT)
sb = linsub(w, 'r', 't')
sbe = w.s([sb], 'eleq1d', '( r = t -> ( %s e. ( 0 (,) 1 ) <-> %s e. ( 0 (,) 1 ) ) )' % (LN('r'), LN('t')))
ar2 = w.s([ar], 'adantr', '( %s -> %s )' % (AT, AR))
aa = w.s([sbe, ar2, to], 'rspcdva', '( %s -> %s e. ( 0 (,) 1 ) )' % (AT, LN('t')))
qc2 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % AT); pc2 = w.s([pc], 'adantr', '( %s -> P e. CC )' % AT)
qp = w.s([qc2, pc2], 'subcld', '( %s -> ( Q - P ) e. CC )' % AT)
AY = '( %s /\\ y e. ( 0 (,) 1 ) )' % PHA
yo = w.s([], 'simpr', '( %s -> y e. ( 0 (,) 1 ) )' % AY)
ssy = closed(w, AY, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
y01 = w.s([ssy, yo], 'sseldd', '( %s -> y e. ( 0 [,] 1 ) )' % AY)
gf2 = w.s([gf], 'adantr', '( %s -> G : ( 0 [,] 1 ) --> CC )' % AY)
hf2 = w.s([hf], 'adantr', '( %s -> H : ( 0 [,] 1 ) --> CC )' % AY)
gv = w.s([gf2, y01], 'ffvelcdmd', '( %s -> ( G ` y ) e. CC )' % AY)
hv = w.s([hf2, y01], 'ffvelcdmd', '( %s -> ( H ` y ) e. CC )' % AY)
da = w.s([pc, qc, w.inst('dvcseglin')], 'syl2anc', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( Q - P ) ) )' % (PHA, LN('t')))
dc0 = w.s(['1'], 'ftc1iccntr', '( %s -> ( RR _D ( y e. ( 0 (,) 1 ) |-> ( G ` y ) ) ) = ( y e. ( 0 (,) 1 ) |-> ( H ` y ) ) )' % HCN)
dc = w.s([hcn, dc0], 'syl', '( %s -> ( RR _D ( y e. ( 0 (,) 1 ) |-> ( G ` y ) ) ) = ( y e. ( 0 (,) 1 ) |-> ( H ` y ) ) )' % PHA)
se = w.s([], 'fveq2', '( y = %s -> ( G ` y ) = ( G ` %s ) )' % (LN('t'), LN('t')))
sf = w.s([], 'fveq2', '( y = %s -> ( H ` y ) = ( H ` %s ) )' % (LN('t'), LN('t')))
w.qed([rr, rr, aa, qp, gv, hv, da, dc, se, sf], 'dvmptco', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> ( G ` %s ) ) ) = ( t e. ( 0 (,) 1 ) |-> %s ) )' % (PHA, LN('t'), HB('t'))); run(w, True)

PHI = '( t e. ( 0 [,] 1 ) |-> ( ( G ` %s ) - ( K ` t ) ) )' % LN('t')
PHIB = '( ( G ` %s ) - ( K ` t ) )' % LN('t')


def phictx(w):
    """the standing context of ditgafflem3/4: the two hypotheses are steps 1, 2"""
    c = {}
    c['hcn'] = w.s([], 'simpl1', '( %s -> %s )' % (PHA, HCN))
    c['p01'] = w.s([], 'simpl2', '( %s -> P e. ( 0 [,] 1 ) )' % PHA)
    c['q01'] = w.s([], 'simpl3', '( %s -> Q e. ( 0 [,] 1 ) )' % PHA)
    c['h3'] = w.s([], 'simpl', '( %s -> %s )' % (PHA, A3))
    c['pc'] = w.s([c['p01'], w.inst('elunitcn')], 'syl', '( %s -> P e. CC )' % PHA)
    c['qc'] = w.s([c['q01'], w.inst('elunitcn')], 'syl', '( %s -> Q e. CC )' % PHA)
    c['hccn'] = w.s([c['h3'], w.inst('ditgafflem1')], 'syl', '( %s -> %s e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (PHA, HC))
    g0 = w.s(['1'], 'ftc1icccn', '( %s -> G e. ( ( 0 [,] 1 ) -cn-> CC ) )' % HCN)
    c['gcn'] = w.s([c['hcn'], g0], 'syl', '( %s -> G e. ( ( 0 [,] 1 ) -cn-> CC ) )' % PHA)
    k0 = w.s(['2'], 'ftc1icccn', '( %s e. ( ( 0 [,] 1 ) -cn-> CC ) -> K e. ( ( 0 [,] 1 ) -cn-> CC ) )' % HC)
    c['kcn'] = w.s([c['hccn'], k0], 'syl', '( %s -> K e. ( ( 0 [,] 1 ) -cn-> CC ) )' % PHA)
    c['gf'] = w.s([c['gcn'], w.inst('cncff')], 'syl', '( %s -> G : ( 0 [,] 1 ) --> CC )' % PHA)
    c['kf'] = w.s([c['kcn'], w.inst('cncff')], 'syl', '( %s -> K : ( 0 [,] 1 ) --> CC )' % PHA)
    c['hf'] = w.s([c['hcn'], w.inst('cncff')], 'syl', '( %s -> H : ( 0 [,] 1 ) --> CC )' % PHA)
    c['hcf'] = w.s([c['hccn'], w.inst('cncff')], 'syl', '( %s -> %s : ( 0 [,] 1 ) --> CC )' % (PHA, HC))
    r0 = w.s([], '0red', '( %s -> 0 e. RR )' % PHA); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % PHA)
    c['r0'] = r0; c['r1'] = r1
    j1 = w.s([r0, r1], 'jca', '( %s -> ( 0 e. RR /\\ 1 e. RR ) )' % PHA)
    j2 = w.s([c['p01'], c['q01']], 'jca', '( %s -> ( P e. ( 0 [,] 1 ) /\\ Q e. ( 0 [,] 1 ) ) )' % PHA)
    c['seg'] = w.s([j1, j2, w.inst('csegicc')], 'syl2anc', '( %s -> ( P cseg Q ) C_ ( 0 [,] 1 ) )' % PHA)
    c['qp'] = w.s([c['qc'], c['pc']], 'subcld', '( %s -> ( Q - P ) e. CC )' % PHA)
    return c


def bodycl(w, c, I):
    """closures of ( G ` LN ( t ) ), ( K ` t ), ( HC ` t ) under ( PHA /\\ t e. I )"""
    A2 = '( %s /\\ t e. %s )' % (PHA, I)
    tt = w.s([], 'simpr', '( %s -> t e. %s )' % (A2, I))
    if I == '( 0 (,) 1 )':
        ss = closed(w, A2, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
        t01 = w.s([ss, tt], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % A2)
    else:
        t01 = tt
    pct = w.s([c['pc']], 'adantr', '( %s -> P e. CC )' % A2)
    qct = w.s([c['qc']], 'adantr', '( %s -> Q e. CC )' % A2)
    lseg = w.s([pct, qct, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( P cseg Q ) )' % (A2, LN('t')))
    segt = w.s([c['seg']], 'adantr', '( %s -> ( P cseg Q ) C_ ( 0 [,] 1 ) )' % A2)
    ln01 = w.s([segt, lseg], 'sseldd', '( %s -> %s e. ( 0 [,] 1 ) )' % (A2, LN('t')))
    gft = w.s([c['gf']], 'adantr', '( %s -> G : ( 0 [,] 1 ) --> CC )' % A2)
    glv = w.s([gft, ln01], 'ffvelcdmd', '( %s -> ( G ` %s ) e. CC )' % (A2, LN('t')))
    kft = w.s([c['kf']], 'adantr', '( %s -> K : ( 0 [,] 1 ) --> CC )' % A2)
    kv = w.s([kft, t01], 'ffvelcdmd', '( %s -> ( K ` t ) e. CC )' % A2)
    hcft = w.s([c['hcf']], 'adantr', '( %s -> %s : ( 0 [,] 1 ) --> CC )' % (A2, HC))
    hcv = w.s([hcft, t01], 'ffvelcdmd', '( %s -> ( %s ` t ) e. CC )' % (A2, HC))
    return t01, glv, kv, hcv


def phival(w, c, x, lnx):
    """closed steps for ( PHI ` x ) = ( ( G ` LN ( x ) ) - ( K ` x ) ), lifted to PHA"""
    l = linsub(w, 't', x)
    f = w.s([l], 'fveq2d', '( t = %s -> ( G ` %s ) = ( G ` %s ) )' % (x, LN('t'), LN(x)))
    k = w.s([], 'fveq2', '( t = %s -> ( K ` t ) = ( K ` %s ) )' % (x, x))
    o = w.s([f, k], 'oveq12d', '( t = %s -> %s = ( ( G ` %s ) - ( K ` %s ) ) )' % (x, PHIB, LN(x), x))
    e = w.s([], 'eqid', '%s = %s' % (PHI, PHI))
    v = w.s([], 'ovex', '( ( G ` %s ) - ( K ` %s ) ) e. _V' % (LN(x), x))
    fv = w.s([o, e, v], 'fvmpt', '( %s e. ( 0 [,] 1 ) -> ( %s ` %s ) = ( ( G ` %s ) - ( K ` %s ) ) )' % (x, PHI, x, LN(x), x))
    el = w.s([], '%selunit' % x, '%s e. ( 0 [,] 1 )' % x)
    mp = w.s([el, fv], 'ax-mp', '( %s ` %s ) = ( ( G ` %s ) - ( K ` %s ) )' % (PHI, x, LN(x), x))
    return w.s([mp], 'a1i', '( %s -> ( %s ` %s ) = ( ( G ` %s ) - ( K ` %s ) ) )' % (PHA, PHI, x, LN(x), x))


# ---- ditgafflem3
w = W('ditgafflem3', 'The two primitives of the reparametrised integrand differ by a constant: their values at the endpoints of the unit interval agree.')
w.s([], 'ditgafflem3.g', 'G = %s' % GDEF, name='h1')
w.s([], 'ditgafflem3.k', 'K = %s' % KDEF, name='h2')
c = phictx(w)
# continuity of the difference of the two primitives
pq = w.s([c['pc'], c['qc']], 'jca', '( %s -> ( P e. CC /\\ Q e. CC ) )' % PHA)
gs = w.s([c['gcn'], c['seg']], 'jca', '( %s -> ( G e. ( ( 0 [,] 1 ) -cn-> CC ) /\\ ( P cseg Q ) C_ ( 0 [,] 1 ) ) )' % PHA)
si = w.s([], 'ssidd', '( %s -> ( 0 [,] 1 ) C_ ( 0 [,] 1 ) )' % PHA)
c1 = w.s([pq, gs, si, w.inst('cseglincnf')], 'syl3anc', '( %s -> ( t e. ( 0 [,] 1 ) |-> ( G ` %s ) ) e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (PHA, LN('t')))
km = w.s([c['kf']], 'feqmptd', '( %s -> K = ( t e. ( 0 [,] 1 ) |-> ( K ` t ) ) )' % PHA)
c2 = w.s([km, c['kcn']], 'eqeltrrd', '( %s -> ( t e. ( 0 [,] 1 ) |-> ( K ` t ) ) e. ( ( 0 [,] 1 ) -cn-> CC ) )' % PHA)
ee, sb = cnop(w, PHA, '-')
c3 = w.s([ee, sb, c1, c2], 'cncfmpt2f', '( %s -> %s e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (PHA, PHI))
# the two derivatives on the open interval
d1 = w.s(['1'], 'ditgafflem2', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> ( G ` %s ) ) ) = ( t e. ( 0 (,) 1 ) |-> %s ) )' % (PHA, LN('t'), HB('t')))
AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % PHA
t01, glv, kv, hcv = bodycl(w, c, '( 0 (,) 1 )')
hcvl = hcval(w, 't')
hcvt = w.s([t01, hcvl], 'syl', '( %s -> ( %s ` t ) = %s )' % (AT, HC, HB('t')))
hcvc = w.s([hcvt], 'eqcomd', '( %s -> %s = ( %s ` t ) )' % (AT, HB('t'), HC))
mp1 = w.s([hcvc], 'mpteq2dva', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) = ( t e. ( 0 (,) 1 ) |-> ( %s ` t ) ) )' % (PHA, HB('t'), HC))
d1b = w.s([d1, mp1], 'eqtrd', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> ( G ` %s ) ) ) = ( t e. ( 0 (,) 1 ) |-> ( %s ` t ) ) )' % (PHA, LN('t'), HC))
dc0 = w.s(['2'], 'ftc1iccntr', '( %s e. ( ( 0 [,] 1 ) -cn-> CC ) -> ( RR _D ( y e. ( 0 (,) 1 ) |-> ( K ` y ) ) ) = ( y e. ( 0 (,) 1 ) |-> ( %s ` y ) ) )' % (HC, HC))
dc = w.s([c['hccn'], dc0], 'syl', '( %s -> ( RR _D ( y e. ( 0 (,) 1 ) |-> ( K ` y ) ) ) = ( y e. ( 0 (,) 1 ) |-> ( %s ` y ) ) )' % (PHA, HC))
kk = w.s([], 'fveq2', '( y = t -> ( K ` y ) = ( K ` t ) )')
cb1 = w.s([kk], 'cbvmptv', '( y e. ( 0 (,) 1 ) |-> ( K ` y ) ) = ( t e. ( 0 (,) 1 ) |-> ( K ` t ) )')
hh = w.s([], 'fveq2', '( y = t -> ( %s ` y ) = ( %s ` t ) )' % (HC, HC))
cb2 = w.s([hh], 'cbvmptv', '( y e. ( 0 (,) 1 ) |-> ( %s ` y ) ) = ( t e. ( 0 (,) 1 ) |-> ( %s ` t ) )' % (HC, HC))
cb1d = w.s([cb1], 'a1i', '( %s -> ( y e. ( 0 (,) 1 ) |-> ( K ` y ) ) = ( t e. ( 0 (,) 1 ) |-> ( K ` t ) ) )' % PHA)
cb2d = w.s([cb2], 'a1i', '( %s -> ( y e. ( 0 (,) 1 ) |-> ( %s ` y ) ) = ( t e. ( 0 (,) 1 ) |-> ( %s ` t ) ) )' % (PHA, HC, HC))
o1 = w.s([cb1d], 'oveq2d', '( %s -> ( RR _D ( y e. ( 0 (,) 1 ) |-> ( K ` y ) ) ) = ( RR _D ( t e. ( 0 (,) 1 ) |-> ( K ` t ) ) ) )' % PHA)
tt1 = w.s([o1, dc], 'eqtr3d', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> ( K ` t ) ) ) = ( y e. ( 0 (,) 1 ) |-> ( %s ` y ) ) )' % (PHA, HC))
d2b = w.s([tt1, cb2d], 'eqtrd', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> ( K ` t ) ) ) = ( t e. ( 0 (,) 1 ) |-> ( %s ` t ) ) )' % (PHA, HC))
rr = closed(w, PHA, 'reelprrecn', 'RR e. { RR , CC }')
dsub = w.s([rr, glv, hcv, d1b, kv, hcv, d2b], 'dvmptsub', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( ( %s ` t ) - ( %s ` t ) ) ) )' % (PHA, PHIB, HC, HC))
sid = w.s([hcv], 'subidd', '( %s -> ( ( %s ` t ) - ( %s ` t ) ) = 0 )' % (AT, HC, HC))
mp2 = w.s([sid], 'mpteq2dva', '( %s -> ( t e. ( 0 (,) 1 ) |-> ( ( %s ` t ) - ( %s ` t ) ) ) = ( t e. ( 0 (,) 1 ) |-> 0 ) )' % (PHA, HC, HC))
dz = w.s([dsub, mp2], 'eqtrd', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> 0 ) )' % (PHA, PHIB))
fcd = closed(w, PHA, 'fconstmpt', '( ( 0 (,) 1 ) X. { 0 } ) = ( t e. ( 0 (,) 1 ) |-> 0 )')
dz2 = w.s([dz, fcd], 'eqtr4d', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( ( 0 (,) 1 ) X. { 0 } ) )' % (PHA, PHIB))
# the derivative of the primitive on the closed interval is the same
AI = '( %s /\\ t e. ( 0 [,] 1 ) )' % PHA
t01i, glvi, kvi, hcvi = bodycl(w, c, '( 0 [,] 1 )')
bodyc = w.s([glvi, kvi], 'subcld', '( %s -> %s e. CC )' % (AI, PHIB))
rc = closed(w, PHA, 'ax-resscn', 'RR C_ CC')
us = closed(w, PHA, 'unitssre', '( 0 [,] 1 ) C_ RR')
ej = w.s([], 'eqid', '%s = %s' % (JR, JR)); ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
nt = closed(w, PHA, 'unitntr', '( ( int ` %s ) ` ( 0 [,] 1 ) ) = ( 0 (,) 1 )' % JR)
ntr = w.s([rc, us, bodyc, ej, ek, nt], 'dvmptntr', '( %s -> ( RR _D %s ) = ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) )' % (PHA, PHI, PHIB))
dv0 = w.s([ntr, dz2], 'eqtrd', '( %s -> ( RR _D %s ) = ( ( 0 (,) 1 ) X. { 0 } ) )' % (PHA, PHI))
deq = w.s([c['r0'], c['r1'], c3, dv0], 'dveq0', '( %s -> %s = ( ( 0 [,] 1 ) X. { ( %s ` 0 ) } ) )' % (PHA, PHI, PHI))
# the values at 1 and 0
v1 = phival(w, c, '1', 'Q')
m1 = w.s([c['qp']], 'mullidd', '( %s -> ( 1 x. ( Q - P ) ) = ( Q - P ) )' % PHA)
o1a = w.s([m1], 'oveq2d', '( %s -> %s = ( P + ( Q - P ) ) )' % (PHA, LN('1')))
pn = w.s([c['pc'], c['qc'], w.inst('pncan3')], 'syl2anc', '( %s -> ( P + ( Q - P ) ) = Q )' % PHA)
ln1 = w.s([o1a, pn], 'eqtrd', '( %s -> %s = Q )' % (PHA, LN('1')))
g1 = w.s([ln1], 'fveq2d', '( %s -> ( G ` %s ) = ( G ` Q ) )' % (PHA, LN('1')))
g1o = w.s([g1], 'oveq1d', '( %s -> ( ( G ` %s ) - ( K ` 1 ) ) = ( ( G ` Q ) - ( K ` 1 ) ) )' % (PHA, LN('1')))
e1 = w.s([v1, g1o], 'eqtrd', '( %s -> ( %s ` 1 ) = ( ( G ` Q ) - ( K ` 1 ) ) )' % (PHA, PHI))
v0 = phival(w, c, '0', 'P')
m0 = w.s([c['qp']], 'mul02d', '( %s -> ( 0 x. ( Q - P ) ) = 0 )' % PHA)
o0a = w.s([m0], 'oveq2d', '( %s -> %s = ( P + 0 ) )' % (PHA, LN('0')))
ad = w.s([c['pc']], 'addridd', '( %s -> ( P + 0 ) = P )' % PHA)
ln0 = w.s([o0a, ad], 'eqtrd', '( %s -> %s = P )' % (PHA, LN('0')))
g0a = w.s([ln0], 'fveq2d', '( %s -> ( G ` %s ) = ( G ` P ) )' % (PHA, LN('0')))
# ( K ` 0 ) = 0
oq = w.s([], 'oveq2', '( u = 0 -> ( 0 (,) u ) = ( 0 (,) 0 ) )')
iq = w.s([oq, w.inst('itgeq1')], 'syl', '( u = 0 -> S. ( 0 (,) u ) ( %s ` s ) _d s = S. ( 0 (,) 0 ) ( %s ` s ) _d s )' % (HC, HC))
ix = w.s([], 'itgex', 'S. ( 0 (,) 0 ) ( %s ` s ) _d s e. _V' % HC)
kf0 = w.s([iq, '2', ix], 'fvmpt', '( 0 e. ( 0 [,] 1 ) -> ( K ` 0 ) = S. ( 0 (,) 0 ) ( %s ` s ) _d s )' % HC)
z0 = w.s([], '0elunit', '0 e. ( 0 [,] 1 )')
k0a = w.s([z0, kf0], 'ax-mp', '( K ` 0 ) = S. ( 0 (,) 0 ) ( %s ` s ) _d s' % HC)
ii = w.s([], 'iooid', '( 0 (,) 0 ) = (/)')
ii2 = w.s([ii, w.inst('itgeq1')], 'ax-mp', 'S. ( 0 (,) 0 ) ( %s ` s ) _d s = S. (/) ( %s ` s ) _d s' % (HC, HC))
iz = w.s([], 'itg0', 'S. (/) ( %s ` s ) _d s = 0' % HC)
k0b = w.s([ii2, iz], 'eqtri', 'S. ( 0 (,) 0 ) ( %s ` s ) _d s = 0' % HC)
k0c = w.s([k0a, k0b], 'eqtri', '( K ` 0 ) = 0')
k0d = w.s([k0c], 'a1i', '( %s -> ( K ` 0 ) = 0 )' % PHA)
o0b = w.s([g0a, k0d], 'oveq12d', '( %s -> ( ( G ` %s ) - ( K ` 0 ) ) = ( ( G ` P ) - 0 ) )' % (PHA, LN('0')))
gpv = w.s([c['gf'], c['p01']], 'ffvelcdmd', '( %s -> ( G ` P ) e. CC )' % PHA)
s1a = w.s([gpv], 'subid1d', '( %s -> ( ( G ` P ) - 0 ) = ( G ` P ) )' % PHA)
o0c = w.s([o0b, s1a], 'eqtrd', '( %s -> ( ( G ` %s ) - ( K ` 0 ) ) = ( G ` P ) )' % (PHA, LN('0')))
e0 = w.s([v0, o0c], 'eqtrd', '( %s -> ( %s ` 0 ) = ( G ` P ) )' % (PHA, PHI))
p0cc = w.s([e0, gpv], 'eqeltrd', '( %s -> ( %s ` 0 ) e. CC )' % (PHA, PHI))
u1 = closed(w, PHA, '1elunit', '1 e. ( 0 [,] 1 )')
fc = w.s([p0cc, u1, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( ( ( 0 [,] 1 ) X. { ( %s ` 0 ) } ) ` 1 ) = ( %s ` 0 ) )' % (PHA, PHI, PHI))
fq = w.s([deq], 'fveq1d', '( %s -> ( %s ` 1 ) = ( ( ( 0 [,] 1 ) X. { ( %s ` 0 ) } ) ` 1 ) )' % (PHA, PHI, PHI))
eq1 = w.s([fq, fc], 'eqtrd', '( %s -> ( %s ` 1 ) = ( %s ` 0 ) )' % (PHA, PHI, PHI))
tz = w.s([e1, eq1], 'eqtr3d', '( %s -> ( ( G ` Q ) - ( K ` 1 ) ) = ( %s ` 0 ) )' % (PHA, PHI))
w.qed([tz, e0], 'eqtrd', '( %s -> ( ( G ` Q ) - ( K ` 1 ) ) = ( G ` P ) )' % PHA); run(w, True)

# ---- ditgafflem4
w = W('ditgafflem4', 'The affine reparametrisation of a directed integral, for an affine map of the open unit interval into itself.')
w.s([], 'ditgafflem4.g', 'G = %s' % GDEF, name='h1')
w.s([], 'ditgafflem4.k', 'K = %s' % KDEF, name='h2')
c = phictx(w)
lem3 = w.s(['1', '2'], 'ditgafflem3', '( %s -> ( ( G ` Q ) - ( K ` 1 ) ) = ( G ` P ) )' % PHA)
ITG1 = 'S. ( 0 (,) 1 ) ( %s ` s ) _d s' % HC
ITG1T = 'S. ( 0 (,) 1 ) ( %s ` t ) _d t' % HC
ITGB = 'S. ( 0 (,) 1 ) %s _d t' % HB('t')
# ( K ` 1 ) is the reparametrised integral
oq = w.s([], 'oveq2', '( u = 1 -> ( 0 (,) u ) = ( 0 (,) 1 ) )')
iq = w.s([oq, w.inst('itgeq1')], 'syl', '( u = 1 -> S. ( 0 (,) u ) ( %s ` s ) _d s = %s )' % (HC, ITG1))
ix = w.s([], 'itgex', '%s e. _V' % ITG1)
kf1 = w.s([iq, '2', ix], 'fvmpt', '( 1 e. ( 0 [,] 1 ) -> ( K ` 1 ) = %s )' % ITG1)
u1c = w.s([], '1elunit', '1 e. ( 0 [,] 1 )')
k1 = w.s([u1c, kf1], 'ax-mp', '( K ` 1 ) = %s' % ITG1)
k1d = w.s([k1], 'a1i', '( %s -> ( K ` 1 ) = %s )' % (PHA, ITG1))
sb = w.s([], 'fveq2', '( s = t -> ( %s ` s ) = ( %s ` t ) )' % (HC, HC))
cbi = w.s([sb], 'cbvitgv', '%s = %s' % (ITG1, ITG1T))
cbid = w.s([cbi], 'a1i', '( %s -> %s = %s )' % (PHA, ITG1, ITG1T))
AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % PHA
to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AT)
sst = closed(w, AT, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
t01 = w.s([sst, to], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % AT)
hcvl = hcval(w, 't')
hcvt = w.s([t01, hcvl], 'syl', '( %s -> ( %s ` t ) = %s )' % (AT, HC, HB('t')))
ie = w.s([hcvt], 'itgeq2dv', '( %s -> %s = %s )' % (PHA, ITG1T, ITGB))
kc1 = w.s([k1d, cbid], 'eqtrd', '( %s -> ( K ` 1 ) = %s )' % (PHA, ITG1T))
kc2 = w.s([kc1, ie], 'eqtrd', '( %s -> ( K ` 1 ) = %s )' % (PHA, ITGB))
# ( G ` Q ) and ( G ` P ) as directed integrals from 0
DQ = 'S_ [ 0 -> Q ] ( H ` s ) _d s'; DP = 'S_ [ 0 -> P ] ( H ` s ) _d s'; DI = 'S_ [ P -> Q ] ( H ` s ) _d s'
def gval(w, x, dx, x01):
    o = w.s([], 'oveq2', '( u = %s -> ( 0 (,) u ) = ( 0 (,) %s ) )' % (x, x))
    i = w.s([o, w.inst('itgeq1')], 'syl', '( u = %s -> S. ( 0 (,) u ) ( H ` s ) _d s = S. ( 0 (,) %s ) ( H ` s ) _d s )' % (x, x))
    e = w.s([], 'itgex', 'S. ( 0 (,) %s ) ( H ` s ) _d s e. _V' % x)
    f = w.s([i, '1', e], 'fvmpt', '( %s e. ( 0 [,] 1 ) -> ( G ` %s ) = S. ( 0 (,) %s ) ( H ` s ) _d s )' % (x, x, x))
    g = w.s([x01, f], 'syl', '( %s -> ( G ` %s ) = S. ( 0 (,) %s ) ( H ` s ) _d s )' % (PHA, x, x))
    b = w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (x, x, x, x))
    t3 = w.s([x01, b], 'sylib', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (PHA, x, x, x))
    le = w.s([t3, w.inst('simp2')], 'syl', '( %s -> 0 <_ %s )' % (PHA, x))
    dp = w.s([le], 'ditgpos', '( %s -> %s = S. ( 0 (,) %s ) ( H ` s ) _d s )' % (PHA, dx, x))
    return w.s([g, dp], 'eqtr4d', '( %s -> ( G ` %s ) = %s )' % (PHA, x, dx))
gqd = gval(w, 'Q', DQ, c['q01'])
gpd = gval(w, 'P', DP, c['p01'])
# splitting the directed integral
z0d = closed(w, PHA, '0elunit', '0 e. ( 0 [,] 1 )')
AS = '( %s /\\ s e. ( 0 (,) 1 ) )' % PHA
so = w.s([], 'simpr', '( %s -> s e. ( 0 (,) 1 ) )' % AS)
sss = closed(w, AS, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
s01 = w.s([sss, so], 'sseldd', '( %s -> s e. ( 0 [,] 1 ) )' % AS)
hfs = w.s([c['hf']], 'adantr', '( %s -> H : ( 0 [,] 1 ) --> CC )' % AS)
hsv = w.s([hfs, s01], 'ffvelcdmd', '( %s -> ( H ` s ) e. CC )' % AS)
ibl = w.s([c['hcn'], w.inst('iblcnunit')], 'syl', '( %s -> ( s e. ( 0 (,) 1 ) |-> ( H ` s ) ) e. L^1 )' % PHA)
spl = w.s([c['r0'], c['r1'], z0d, c['p01'], c['q01'], hsv, ibl], 'ditgsplit', '( %s -> %s = ( %s + %s ) )' % (PHA, DQ, DP, DI))
icl = w.s([c['r0'], c['r1'], c['p01'], c['q01'], hsv, ibl], 'ditgcl', '( %s -> %s e. CC )' % (PHA, DI))
sp2 = w.s([gqd, spl], 'eqtrd', '( %s -> ( G ` Q ) = ( %s + %s ) )' % (PHA, DP, DI))
gpc = w.s([gpd], 'eqcomd', '( %s -> %s = ( G ` P ) )' % (PHA, DP))
sp2b = w.s([gpc], 'oveq1d', '( %s -> ( %s + %s ) = ( ( G ` P ) + %s ) )' % (PHA, DP, DI, DI))
sp3 = w.s([sp2, sp2b], 'eqtrd', '( %s -> ( G ` Q ) = ( ( G ` P ) + %s ) )' % (PHA, DI))
ov = w.s([sp3], 'oveq1d', '( %s -> ( ( G ` Q ) - ( G ` P ) ) = ( ( ( G ` P ) + %s ) - ( G ` P ) ) )' % (PHA, DI))
gpv = w.s([c['gf'], c['p01']], 'ffvelcdmd', '( %s -> ( G ` P ) e. CC )' % PHA)
gqv = w.s([c['gf'], c['q01']], 'ffvelcdmd', '( %s -> ( G ` Q ) e. CC )' % PHA)
u1d = closed(w, PHA, '1elunit', '1 e. ( 0 [,] 1 )')
k1v = w.s([c['kf'], u1d], 'ffvelcdmd', '( %s -> ( K ` 1 ) e. CC )' % PHA)
pnc = w.s([gpv, icl], 'pncan2d', '( %s -> ( ( ( G ` P ) + %s ) - ( G ` P ) ) = %s )' % (PHA, DI, DI))
e2 = w.s([ov, pnc], 'eqtrd', '( %s -> ( ( G ` Q ) - ( G ` P ) ) = %s )' % (PHA, DI))
ss23 = w.s([gqv, k1v, gpv, w.inst('subsub23')], 'syl3anc', '( %s -> ( ( ( G ` Q ) - ( K ` 1 ) ) = ( G ` P ) <-> ( ( G ` Q ) - ( G ` P ) ) = ( K ` 1 ) ) )' % PHA)
k1e = w.s([lem3, ss23], 'mpbid', '( %s -> ( ( G ` Q ) - ( G ` P ) ) = ( K ` 1 ) )' % PHA)
di1 = w.s([e2, k1e], 'eqtr3d', '( %s -> %s = ( K ` 1 ) )' % (PHA, DI))
di2 = w.s([di1, kc2], 'eqtrd', '( %s -> %s = %s )' % (PHA, DI, ITGB))
w.qed([di2], 'eqcomd', '( %s -> %s = %s )' % (PHA, ITGB, DI)); run(w, True)

# ---- ditgaff
ITGB = 'S. ( 0 (,) 1 ) %s _d t' % HB('t')
DI = 'S_ [ P -> Q ] ( H ` s ) _d s'


def a3ctx(w, ante):
    """the conjuncts of A3 and the real bounds of P and Q under ( A3 /\\ X )"""
    c = {}
    bare = ante == A3
    c['hcn'] = w.s([], 'simp1' if bare else 'simpl1', '( %s -> %s )' % (ante, HCN))
    c['p01'] = w.s([], 'simp2' if bare else 'simpl2', '( %s -> P e. ( 0 [,] 1 ) )' % ante)
    c['q01'] = w.s([], 'simp3' if bare else 'simpl3', '( %s -> Q e. ( 0 [,] 1 ) )' % ante)
    c['h3'] = w.s([], 'id' if bare else 'simpl', '( %s -> %s )' % (ante, A3))
    for v, st in (('P', c['p01']), ('Q', c['q01'])):
        b = w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (v, v, v, v))
        t3 = w.s([st, b], 'sylib', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (ante, v, v, v))
        c[v + 'r'] = w.s([t3, w.inst('simp1')], 'syl', '( %s -> %s e. RR )' % (ante, v))
        c[v + '0'] = w.s([t3, w.inst('simp2')], 'syl', '( %s -> 0 <_ %s )' % (ante, v))
        c[v + '1'] = w.s([t3, w.inst('simp3')], 'syl', '( %s -> %s <_ 1 )' % (ante, v))
    c['pc'] = w.s([c['p01'], w.inst('elunitcn')], 'syl', '( %s -> P e. CC )' % ante)
    c['qc'] = w.s([c['q01'], w.inst('elunitcn')], 'syl', '( %s -> Q e. CC )' % ante)
    return c


def iooin(w, ante, lo, hi, lostep, histep):
    """( ante -> ( lo (,) hi ) C_ ( 0 (,) 1 ) ) from 0 <_ lo and hi <_ 1"""
    x0 = closed(w, ante, '0xr', '0 e. RR*'); x1 = closed(w, ante, '1xr', '1 e. RR*')
    j1 = w.s([x0, x1], 'jca', '( %s -> ( 0 e. RR* /\\ 1 e. RR* ) )' % ante)
    j2 = w.s([lostep, histep], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ 1 ) )' % (ante, lo, hi))
    return w.s([j1, j2, w.inst('ioossioo')], 'syl2anc', '( %s -> ( %s (,) %s ) C_ ( 0 (,) 1 ) )' % (ante, lo, hi))


def applylem4(w, ante, arstep):
    """( ante -> DI = ITGB ) from a step proving ( ante -> AR )"""
    pha = w.s([w.s([], 'simpl', '( %s -> %s )' % (ante, A3)), arstep], 'jca', '( %s -> %s )' % (ante, PHA))
    eg = w.s([], 'eqid', '%s = %s' % (GDEF, GDEF))
    ek = w.s([], 'eqid', '%s = %s' % (KDEF, KDEF))
    l4 = w.s([eg, ek], 'ditgafflem4', '( %s -> %s = %s )' % (PHA, ITGB, DI))
    st = w.s([pha, l4], 'syl', '( %s -> %s = %s )' % (ante, ITGB, DI))
    return w.s([st], 'eqcomd', '( %s -> %s = %s )' % (ante, DI, ITGB))


w = W('ditgaff', 'The affine reparametrisation of a directed integral over a subinterval of the unit interval: the directed integral from P to Q of a continuous function is the integral over the unit interval of the reparametrised integrand.')
# case P < Q
C1 = '( %s /\\ P < Q )' % A3
c = a3ctx(w, C1)
lt = w.s([], 'simpr', '( %s -> P < Q )' % C1)
AC1 = '( %s /\\ r e. ( 0 (,) 1 ) )' % C1
ro = w.s([], 'simpr', '( %s -> r e. ( 0 (,) 1 ) )' % AC1)
pr2 = w.s([c['Pr']], 'adantr', '( %s -> P e. RR )' % AC1); qr2 = w.s([c['Qr']], 'adantr', '( %s -> Q e. RR )' % AC1)
lt2 = w.s([lt], 'adantr', '( %s -> P < Q )' % AC1)
t3 = w.s([pr2, qr2, lt2], '3jca', '( %s -> ( P e. RR /\\ Q e. RR /\\ P < Q ) )' % AC1)
il = w.s([t3, ro, w.inst('ioolin')], 'syl2anc', '( %s -> %s e. ( P (,) Q ) )' % (AC1, LN('r')))
p02 = w.s([c['P0']], 'adantr', '( %s -> 0 <_ P )' % AC1); q12 = w.s([c['Q1']], 'adantr', '( %s -> Q <_ 1 )' % AC1)
ss = iooin(w, AC1, 'P', 'Q', p02, q12)
inn = w.s([ss, il], 'sseldd', '( %s -> %s e. ( 0 (,) 1 ) )' % (AC1, LN('r')))
ar1 = w.s([inn], 'ralrimiva', '( %s -> %s )' % (C1, AR))
case1 = applylem4(w, C1, ar1)
# case P = Q
C2 = '( %s /\\ P = Q )' % A3
c2 = a3ctx(w, C2)
eq = w.s([], 'simpr', '( %s -> P = Q )' % C2)
le = w.s([c2['Pr'], eq], 'eqled', '( %s -> P <_ Q )' % C2)
dp = w.s([le], 'ditgpos', '( %s -> %s = S. ( P (,) Q ) ( H ` s ) _d s )' % (C2, DI))
qeq = w.s([eq], 'eqcomd', '( %s -> Q = P )' % C2)
oi = w.s([qeq], 'oveq2d', '( %s -> ( P (,) Q ) = ( P (,) P ) )' % C2)
ii = closed(w, C2, 'iooid', '( P (,) P ) = (/)')
oi2 = w.s([oi, ii], 'eqtrd', '( %s -> ( P (,) Q ) = (/) )' % C2)
ie1 = w.s([oi2], 'itgeq1d', '( %s -> S. ( P (,) Q ) ( H ` s ) _d s = S. (/) ( H ` s ) _d s )' % C2)
iz1 = closed(w, C2, 'itg0', 'S. (/) ( H ` s ) _d s = 0')
lhs = w.s([w.s([dp, ie1], 'eqtrd', '( %s -> %s = S. (/) ( H ` s ) _d s )' % (C2, DI)), iz1], 'eqtrd', '( %s -> %s = 0 )' % (C2, DI))
qp0a = w.s([qeq], 'oveq1d', '( %s -> ( Q - P ) = ( P - P ) )' % C2)
qp0b = w.s([c2['pc']], 'subidd', '( %s -> ( P - P ) = 0 )' % C2)
qp0 = w.s([qp0a, qp0b], 'eqtrd', '( %s -> ( Q - P ) = 0 )' % C2)
AC2 = '( %s /\\ t e. ( 0 (,) 1 ) )' % C2
to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AC2)
sst = closed(w, AC2, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
t01 = w.s([sst, to], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % AC2)
pc2 = w.s([c2['pc']], 'adantr', '( %s -> P e. CC )' % AC2); qc2 = w.s([c2['qc']], 'adantr', '( %s -> Q e. CC )' % AC2)
lseg = w.s([pc2, qc2, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( P cseg Q ) )' % (AC2, LN('t')))
r0b = w.s([], '0red', '( %s -> 0 e. RR )' % C2); r1b = w.s([], '1red', '( %s -> 1 e. RR )' % C2)
jj1 = w.s([r0b, r1b], 'jca', '( %s -> ( 0 e. RR /\\ 1 e. RR ) )' % C2)
jj2 = w.s([c2['p01'], c2['q01']], 'jca', '( %s -> ( P e. ( 0 [,] 1 ) /\\ Q e. ( 0 [,] 1 ) ) )' % C2)
seg = w.s([jj1, jj2, w.inst('csegicc')], 'syl2anc', '( %s -> ( P cseg Q ) C_ ( 0 [,] 1 ) )' % C2)
seg2 = w.s([seg], 'adantr', '( %s -> ( P cseg Q ) C_ ( 0 [,] 1 ) )' % AC2)
ln01 = w.s([seg2, lseg], 'sseldd', '( %s -> %s e. ( 0 [,] 1 ) )' % (AC2, LN('t')))
hf2 = w.s([w.s([c2['hcn'], w.inst('cncff')], 'syl', '( %s -> H : ( 0 [,] 1 ) --> CC )' % C2)], 'adantr', '( %s -> H : ( 0 [,] 1 ) --> CC )' % AC2)
hv = w.s([hf2, ln01], 'ffvelcdmd', '( %s -> ( H ` %s ) e. CC )' % (AC2, LN('t')))
qp02 = w.s([qp0], 'adantr', '( %s -> ( Q - P ) = 0 )' % AC2)
ob = w.s([qp02], 'oveq2d', '( %s -> %s = ( ( H ` %s ) x. 0 ) )' % (AC2, HB('t'), LN('t')))
m0 = w.s([hv], 'mul01d', '( %s -> ( ( H ` %s ) x. 0 ) = 0 )' % (AC2, LN('t')))
ob2 = w.s([ob, m0], 'eqtrd', '( %s -> %s = 0 )' % (AC2, HB('t')))
ie2 = w.s([ob2], 'itgeq2dv', '( %s -> %s = S. ( 0 (,) 1 ) 0 _d t )' % (C2, ITGB))
iz2 = closed(w, C2, 'itgz', 'S. ( 0 (,) 1 ) 0 _d t = 0')
rhs = w.s([ie2, iz2], 'eqtrd', '( %s -> %s = 0 )' % (C2, ITGB))
case2 = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s = %s )' % (C2, DI, ITGB))
# case Q < P
C3 = '( %s /\\ Q < P )' % A3
c3 = a3ctx(w, C3)
gt = w.s([], 'simpr', '( %s -> Q < P )' % C3)
AC3 = '( %s /\\ r e. ( 0 (,) 1 ) )' % C3
ro3 = w.s([], 'simpr', '( %s -> r e. ( 0 (,) 1 ) )' % AC3)
rev = w.s([ro3, w.inst('iooirev')], 'syl', '( %s -> ( 1 - r ) e. ( 0 (,) 1 ) )' % AC3)
pr3 = w.s([c3['Pr']], 'adantr', '( %s -> P e. RR )' % AC3); qr3 = w.s([c3['Qr']], 'adantr', '( %s -> Q e. RR )' % AC3)
gt2 = w.s([gt], 'adantr', '( %s -> Q < P )' % AC3)
t33 = w.s([qr3, pr3, gt2], '3jca', '( %s -> ( Q e. RR /\\ P e. RR /\\ Q < P ) )' % AC3)
REV = '( Q + ( ( 1 - r ) x. ( P - Q ) ) )'
il3 = w.s([t33, rev, w.inst('ioolin')], 'syl2anc', '( %s -> %s e. ( Q (,) P ) )' % (AC3, REV))
q03 = w.s([c3['Q0']], 'adantr', '( %s -> 0 <_ Q )' % AC3); p13 = w.s([c3['P1']], 'adantr', '( %s -> P <_ 1 )' % AC3)
ss3 = iooin(w, AC3, 'Q', 'P', q03, p13)
in3 = w.s([ss3, il3], 'sseldd', '( %s -> %s e. ( 0 (,) 1 ) )' % (AC3, REV))
qc3 = w.s([c3['qc']], 'adantr', '( %s -> Q e. CC )' % AC3); pc3 = w.s([c3['pc']], 'adantr', '( %s -> P e. CC )' % AC3)
rc3 = w.s([ro3, w.inst('elioore')], 'syl', '( %s -> r e. RR )' % AC3)
rcc = w.s([rc3], 'recnd', '( %s -> r e. CC )' % AC3)
crv = w.s([qc3, pc3, rcc, w.inst('cseglinrev')], 'syl3anc', '( %s -> %s = %s )' % (AC3, REV, LN('r')))
in3b = w.s([crv, in3], 'eqeltrrd', '( %s -> %s e. ( 0 (,) 1 ) )' % (AC3, LN('r')))
ar3 = w.s([in3b], 'ralrimiva', '( %s -> %s )' % (C3, AR))
case3 = applylem4(w, C3, ar3)
# trichotomy
ca = a3ctx(w, A3)
tri = w.s([ca['Pr'], ca['Qr'], w.inst('lttri4')], 'syl2anc', '( %s -> ( P < Q \\/ P = Q \\/ Q < P ) )' % A3)
w.qed([case1, case2, case3, tri], 'mpjao3dan', '( %s -> %s = %s )' % (A3, DI, ITGB)); run(w)
