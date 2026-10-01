"""Sortie C0, batch 7: the fundamental theorem of calculus for the segment
integral (lintftc)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w, h=False):
    if only and w.label not in only: return True
    return runh(w) if h else w.run()

PHF = ('( ( A e. CC /\\ B e. CC ) /\\ ( G : U --> CC /\\ ( CC _D G ) = F ) /\\ '
       '( F e. ( U -cn-> CC ) /\\ ( A cseg B ) C_ U ) )')
PHI = '( w e. ( 0 [,] 1 ) |-> ( G ` %s ) )' % LIN('A', 'B', 'w')
def IG(x): return INTG('F', 'A', 'B', x)
IMPT = '( w e. ( 0 (,) 1 ) |-> %s )' % IG('w')

w = W('lintftc', 'The fundamental theorem of calculus for the segment integral: the integral of a continuous derivative along a segment is the difference of the values of the primitive at the endpoints.')
a = w.s([], 'simp1l', '( %s -> A e. CC )' % PHF); b = w.s([], 'simp1r', '( %s -> B e. CC )' % PHF)
gf = w.s([], 'simp2l', '( %s -> G : U --> CC )' % PHF)
dvg = w.s([], 'simp2r', '( %s -> ( CC _D G ) = F )' % PHF)
fcn = w.s([], 'simp3l', '( %s -> F e. ( U -cn-> CC ) )' % PHF)
sg = w.s([], 'simp3r', '( %s -> ( A cseg B ) C_ U )' % PHF)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : U --> CC )' % PHF)
uc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> U C_ CC )' % PHF)
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % PHF)
# G is continuous on U: it is differentiable at every point of U
fdm = w.s([ff, w.inst('fdm')], 'syl', '( %s -> dom F = U )' % PHF)
dmd = w.s([dvg], 'dmeqd', '( %s -> dom ( CC _D G ) = dom F )' % PHF)
dvdm = w.s([dmd, fdm], 'eqtrd', '( %s -> dom ( CC _D G ) = U )' % PHF)
ccs = w.s([], 'ssidd', '( %s -> CC C_ CC )' % PHF)
j3 = w.s([ccs, gf, uc], '3jca', '( %s -> ( CC C_ CC /\\ G : U --> CC /\\ U C_ CC ) )' % PHF)
gcn = w.s([j3, dvdm, w.inst('dvcn')], 'syl2anc', '( %s -> G e. ( U -cn-> CC ) )' % PHF)
# the parametrised primitive is continuous on the closed unit interval
ab = w.s([a, b], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % PHF)
gs = w.s([gcn, sg], 'jca', '( %s -> ( G e. ( U -cn-> CC ) /\\ ( A cseg B ) C_ U ) )' % PHF)
si = w.s([], 'ssidd', '( %s -> ( 0 [,] 1 ) C_ ( 0 [,] 1 ) )' % PHF)
pc0 = w.s([ab, gs, si, w.inst('cseglincnf')], 'syl3anc', '( %s -> ( t e. ( 0 [,] 1 ) |-> ( G ` %s ) ) e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (PHF, LIN('A', 'B', 't')))


def lsub(w, frm, to):
    e = w.s([], 'oveq1', '( %s = %s -> ( %s x. ( B - A ) ) = ( %s x. ( B - A ) ) )' % (frm, to, frm, to))
    return w.s([e], 'oveq2d', '( %s = %s -> %s = %s )' % (frm, to, LIN('A', 'B', frm), LIN('A', 'B', to)))


def gsub(w, frm, to):
    l = lsub(w, frm, to)
    return w.s([l], 'fveq2d', '( %s = %s -> ( G ` %s ) = ( G ` %s ) )' % (frm, to, LIN('A', 'B', frm), LIN('A', 'B', to)))


def isub(w, frm, to):
    l = lsub(w, frm, to)
    f = w.s([l], 'fveq2d', '( %s = %s -> ( F ` %s ) = ( F ` %s ) )' % (frm, to, LIN('A', 'B', frm), LIN('A', 'B', to)))
    return w.s([f], 'oveq1d', '( %s = %s -> %s = %s )' % (frm, to, IG(frm), IG(to)))


cbg = w.s([gsub(w, 't', 'w')], 'cbvmptv', '( t e. ( 0 [,] 1 ) |-> ( G ` %s ) ) = %s' % (LIN('A', 'B', 't'), PHI))
cbgd = w.s([cbg], 'a1i', '( %s -> ( t e. ( 0 [,] 1 ) |-> ( G ` %s ) ) = %s )' % (PHF, LIN('A', 'B', 't'), PHI))
phicn = w.s([cbgd, pc0], 'eqeltrrd', '( %s -> %s e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (PHF, PHI))
# the derivative of the parametrisation, in the variable w
dv0 = w.s([a, b, w.inst('dvcseglin')], 'syl2anc', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( B - A ) ) )' % (PHF, LIN('A', 'B', 't')))
cbl = w.s([lsub(w, 't', 'w')], 'cbvmptv', '( t e. ( 0 (,) 1 ) |-> %s ) = ( w e. ( 0 (,) 1 ) |-> %s )' % (LIN('A', 'B', 't'), LIN('A', 'B', 'w')))
eqc = w.s([], 'eqid', '( B - A ) = ( B - A )')
eqci = w.s([eqc], 'a1i', '( t = w -> ( B - A ) = ( B - A ) )')
cbc = w.s([eqci], 'cbvmptv', '( t e. ( 0 (,) 1 ) |-> ( B - A ) ) = ( w e. ( 0 (,) 1 ) |-> ( B - A ) )')
cbld = w.s([cbl], 'a1i', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) = ( w e. ( 0 (,) 1 ) |-> %s ) )' % (PHF, LIN('A', 'B', 't'), LIN('A', 'B', 'w')))
cbcd = w.s([cbc], 'a1i', '( %s -> ( t e. ( 0 (,) 1 ) |-> ( B - A ) ) = ( w e. ( 0 (,) 1 ) |-> ( B - A ) ) )' % PHF)
ov1 = w.s([cbld], 'oveq2d', '( %s -> ( RR _D ( t e. ( 0 (,) 1 ) |-> %s ) ) = ( RR _D ( w e. ( 0 (,) 1 ) |-> %s ) ) )' % (PHF, LIN('A', 'B', 't'), LIN('A', 'B', 'w')))
dvw0 = w.s([ov1, dv0], 'eqtr3d', '( %s -> ( RR _D ( w e. ( 0 (,) 1 ) |-> %s ) ) = ( t e. ( 0 (,) 1 ) |-> ( B - A ) ) )' % (PHF, LIN('A', 'B', 'w')))
dvw = w.s([dvw0, cbcd], 'eqtrd', '( %s -> ( RR _D ( w e. ( 0 (,) 1 ) |-> %s ) ) = ( w e. ( 0 (,) 1 ) |-> ( B - A ) ) )' % (PHF, LIN('A', 'B', 'w')))
# the chain rule
rr = closed(w, PHF, 'reelprrecn', 'RR e. { RR , CC }')
cpr = closed(w, PHF, 'cnelprrecn', 'CC e. { RR , CC }')
AW = '( %s /\\ w e. ( 0 (,) 1 ) )' % PHF
wo = w.s([], 'simpr', '( %s -> w e. ( 0 (,) 1 ) )' % AW)
ssw = closed(w, AW, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
w01 = w.s([ssw, wo], 'sseldd', '( %s -> w e. ( 0 [,] 1 ) )' % AW)
aw = w.s([a], 'adantr', '( %s -> A e. CC )' % AW); bw = w.s([b], 'adantr', '( %s -> B e. CC )' % AW)
lsg = w.s([aw, bw, w01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (AW, LIN('A', 'B', 'w')))
sgw = w.s([sg], 'adantr', '( %s -> ( A cseg B ) C_ U )' % AW)
lnu = w.s([sgw, lsg], 'sseldd', '( %s -> %s e. U )' % (AW, LIN('A', 'B', 'w')))
baw = w.s([ba], 'adantr', '( %s -> ( B - A ) e. CC )' % AW)
AU = '( %s /\\ y e. U )' % PHF
yu = w.s([], 'simpr', '( %s -> y e. U )' % AU)
gfu = w.s([gf], 'adantr', '( %s -> G : U --> CC )' % AU); ffu = w.s([ff], 'adantr', '( %s -> F : U --> CC )' % AU)
gv = w.s([gfu, yu], 'ffvelcdmd', '( %s -> ( G ` y ) e. CC )' % AU)
fv = w.s([ffu, yu], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % AU)
gm = w.s([gf], 'feqmptd', '( %s -> G = ( y e. U |-> ( G ` y ) ) )' % PHF)
fm = w.s([ff], 'feqmptd', '( %s -> F = ( y e. U |-> ( F ` y ) ) )' % PHF)
og = w.s([gm], 'oveq2d', '( %s -> ( CC _D G ) = ( CC _D ( y e. U |-> ( G ` y ) ) ) )' % PHF)
dg = w.s([dvg, fm], 'eqtrd', '( %s -> ( CC _D G ) = ( y e. U |-> ( F ` y ) ) )' % PHF)
dcc = w.s([og, dg], 'eqtr3d', '( %s -> ( CC _D ( y e. U |-> ( G ` y ) ) ) = ( y e. U |-> ( F ` y ) ) )' % PHF)
se = w.s([], 'fveq2', '( y = %s -> ( G ` y ) = ( G ` %s ) )' % (LIN('A', 'B', 'w'), LIN('A', 'B', 'w')))
sf = w.s([], 'fveq2', '( y = %s -> ( F ` y ) = ( F ` %s ) )' % (LIN('A', 'B', 'w'), LIN('A', 'B', 'w')))
dvco = w.s([rr, cpr, lnu, baw, gv, fv, dvw, dcc, se, sf], 'dvmptco', '( %s -> ( RR _D ( w e. ( 0 (,) 1 ) |-> ( G ` %s ) ) ) = %s )' % (PHF, LIN('A', 'B', 'w'), IMPT))
# from the closed to the open interval
rc = closed(w, PHF, 'ax-resscn', 'RR C_ CC')
us = closed(w, PHF, 'unitssre', '( 0 [,] 1 ) C_ RR')
AI = '( %s /\\ w e. ( 0 [,] 1 ) )' % PHF
wi = w.s([], 'simpr', '( %s -> w e. ( 0 [,] 1 ) )' % AI)
ai = w.s([a], 'adantr', '( %s -> A e. CC )' % AI); bi = w.s([b], 'adantr', '( %s -> B e. CC )' % AI)
lsgi = w.s([ai, bi, wi, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (AI, LIN('A', 'B', 'w')))
sgi = w.s([sg], 'adantr', '( %s -> ( A cseg B ) C_ U )' % AI)
lnui = w.s([sgi, lsgi], 'sseldd', '( %s -> %s e. U )' % (AI, LIN('A', 'B', 'w')))
gfi = w.s([gf], 'adantr', '( %s -> G : U --> CC )' % AI)
gvi = w.s([gfi, lnui], 'ffvelcdmd', '( %s -> ( G ` %s ) e. CC )' % (AI, LIN('A', 'B', 'w')))
ej = w.s([], 'eqid', '%s = %s' % (JR, JR)); ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
nt = closed(w, PHF, 'unitntr', '( ( int ` %s ) ` ( 0 [,] 1 ) ) = ( 0 (,) 1 )' % JR)
ntr = w.s([rc, us, gvi, ej, ek, nt], 'dvmptntr', '( %s -> ( RR _D %s ) = ( RR _D ( w e. ( 0 (,) 1 ) |-> ( G ` %s ) ) ) )' % (PHF, PHI, LIN('A', 'B', 'w')))
dvphi = w.s([ntr, dvco], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (PHF, PHI, IMPT))
# continuity and integrability of the integrand
cbi = w.s([isub(w, 't', 'w')], 'cbvmptv', '( t e. ( 0 (,) 1 ) |-> %s ) = %s' % (IG('t'), IMPT))
cbid = w.s([cbi], 'a1i', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) = %s )' % (PHF, IG('t'), IMPT))
sso = closed(w, PHF, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
fs = w.s([fcn, sg], 'jca', '( %s -> ( F e. ( U -cn-> CC ) /\\ ( A cseg B ) C_ U ) )' % PHF)
icn0 = w.s([ab, fs, sso, w.inst('lintcnlem')], 'syl3anc', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) e. ( ( 0 (,) 1 ) -cn-> CC ) )' % (PHF, IG('t')))
icn = w.s([cbid, icn0], 'eqeltrrd', '( %s -> %s e. ( ( 0 (,) 1 ) -cn-> CC ) )' % (PHF, IMPT))
ph2 = w.s([ab, fs], 'jca', '( %s -> ( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( U -cn-> CC ) /\\ ( A cseg B ) C_ U ) ) )' % PHF)
ibl0 = w.s([ph2, w.inst('lintibl')], 'syl', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) e. L^1 )' % (PHF, IG('t')))
ibl = w.s([cbid, ibl0], 'eqeltrrd', '( %s -> %s e. L^1 )' % (PHF, IMPT))
dc = w.s([dvphi, icn], 'eqeltrd', '( %s -> ( RR _D %s ) e. ( ( 0 (,) 1 ) -cn-> CC ) )' % (PHF, PHI))
di = w.s([dvphi, ibl], 'eqeltrd', '( %s -> ( RR _D %s ) e. L^1 )' % (PHF, PHI))
# the second fundamental theorem
r0 = w.s([], '0red', '( %s -> 0 e. RR )' % PHF); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % PHF)
le = closed(w, PHF, '0le1', '0 <_ 1')
f2 = w.s([r0, r1, le, dc, di, phicn], 'ftc2', '( %s -> S. ( 0 (,) 1 ) ( ( RR _D %s ) ` t ) _d t = ( ( %s ` 1 ) - ( %s ` 0 ) ) )' % (PHF, PHI, PHI, PHI))
# the integrand of the segment integral
AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % PHF
to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AT)
fq = w.s([dvphi], 'fveq1d', '( %s -> ( ( RR _D %s ) ` t ) = ( %s ` t ) )' % (PHF, PHI, IMPT))
fq2 = w.s([fq], 'adantr', '( %s -> ( ( RR _D %s ) ` t ) = ( %s ` t ) )' % (AT, PHI, IMPT))
eqm = w.s([], 'eqid', '%s = %s' % (IMPT, IMPT))
ovx = w.s([], 'ovex', '%s e. _V' % IG('t'))
fvm = w.s([isub(w, 'w', 't'), eqm, ovx], 'fvmpt', '( t e. ( 0 (,) 1 ) -> ( %s ` t ) = %s )' % (IMPT, IG('t')))
fvm2 = w.s([to, fvm], 'syl', '( %s -> ( %s ` t ) = %s )' % (AT, IMPT, IG('t')))
pw = w.s([fq2, fvm2], 'eqtrd', '( %s -> ( ( RR _D %s ) ` t ) = %s )' % (AT, PHI, IG('t')))
ie = w.s([pw], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) ( ( RR _D %s ) ` t ) _d t = S. ( 0 (,) 1 ) %s _d t )' % (PHF, PHI, IG('t')))
lv = w.s([fcn, a, b, w.inst('lintval')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PHF, LINT('F', 'A', 'B'), IG('t')))
# the values of the parametrised primitive at the endpoints


def phiv(w, x, val, elun, zero):
    eqi = w.s([], 'eqid', '%s = %s' % (PHI, PHI))
    vx = w.s([], 'fvex', '( G ` %s ) e. _V' % LIN('A', 'B', x))
    fvp = w.s([gsub(w, 'w', x), eqi, vx], 'fvmpt', '( %s e. ( 0 [,] 1 ) -> ( %s ` %s ) = ( G ` %s ) )' % (x, PHI, x, LIN('A', 'B', x)))
    el = w.s([], elun, '%s e. ( 0 [,] 1 )' % x)
    mp = w.s([el, fvp], 'ax-mp', '( %s ` %s ) = ( G ` %s )' % (PHI, x, LIN('A', 'B', x)))
    mpd = w.s([mp], 'a1i', '( %s -> ( %s ` %s ) = ( G ` %s ) )' % (PHF, PHI, x, LIN('A', 'B', x)))
    if zero:
        m = w.s([ba], 'mul02d', '( %s -> ( %s x. ( B - A ) ) = 0 )' % (PHF, x))
        o = w.s([m], 'oveq2d', '( %s -> %s = ( A + 0 ) )' % (PHF, LIN('A', 'B', x)))
        e = w.s([a], 'addridd', '( %s -> ( A + 0 ) = A )' % PHF)
    else:
        m = w.s([ba], 'mullidd', '( %s -> ( %s x. ( B - A ) ) = ( B - A ) )' % (PHF, x))
        o = w.s([m], 'oveq2d', '( %s -> %s = ( A + ( B - A ) ) )' % (PHF, LIN('A', 'B', x)))
        e = w.s([a, b, w.inst('pncan3')], 'syl2anc', '( %s -> ( A + ( B - A ) ) = B )' % PHF)
    ln = w.s([o, e], 'eqtrd', '( %s -> %s = %s )' % (PHF, LIN('A', 'B', x), val))
    gv2 = w.s([ln], 'fveq2d', '( %s -> ( G ` %s ) = ( G ` %s ) )' % (PHF, LIN('A', 'B', x), val))
    return w.s([mpd, gv2], 'eqtrd', '( %s -> ( %s ` %s ) = ( G ` %s ) )' % (PHF, PHI, x, val))


p1v = phiv(w, '1', 'B', '1elunit', False)
p0v = phiv(w, '0', 'A', '0elunit', True)
ov = w.s([p1v, p0v], 'oveq12d', '( %s -> ( ( %s ` 1 ) - ( %s ` 0 ) ) = ( ( G ` B ) - ( G ` A ) ) )' % (PHF, PHI, PHI))
x1 = w.s([ie, f2], 'eqtr3d', '( %s -> S. ( 0 (,) 1 ) %s _d t = ( ( %s ` 1 ) - ( %s ` 0 ) ) )' % (PHF, IG('t'), PHI, PHI))
x2 = w.s([x1, ov], 'eqtrd', '( %s -> S. ( 0 (,) 1 ) %s _d t = ( ( G ` B ) - ( G ` A ) ) )' % (PHF, IG('t')))
w.qed([lv, x2], 'eqtrd', '( %s -> %s = ( ( G ` B ) - ( G ` A ) ) )' % (PHF, LINT('F', 'A', 'B'))); run(w)
