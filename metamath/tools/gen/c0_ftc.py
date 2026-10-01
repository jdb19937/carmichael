"""Sortie C0, batch 4: the FTC on the closed unit interval (ftc1icc, ftc1icccn,
ftc1iccntr)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return runh(w)

HCN = 'H e. ( ( 0 [,] 1 ) -cn-> CC )'
HR = '( y e. ( 0 (,) 1 ) |-> ( H ` y ) )'
HI = '( y e. ( 0 [,] 1 ) |-> ( H ` y ) )'
GDEF = '( u e. ( 0 [,] 1 ) |-> S. ( 0 (,) u ) ( H ` s ) _d s )'
GDEFR = '( u e. ( 0 [,] 1 ) |-> S. ( 0 (,) u ) ( %s ` s ) _d s )' % HR


def grewrite(w):
    """closed step: GDEF = GDEFR, the integrand rewritten through the restriction HR"""
    au = 'u e. ( 0 [,] 1 )'
    idu = w.s([], 'id', '( %s -> %s )' % (au, au))
    b = w.s([], 'elicc01', '( u e. ( 0 [,] 1 ) <-> ( u e. RR /\\ 0 <_ u /\\ u <_ 1 ) )')
    t = w.s([idu, b], 'sylib', '( %s -> ( u e. RR /\\ 0 <_ u /\\ u <_ 1 ) )' % au)
    u1 = w.s([t, w.inst('simp3')], 'syl', '( %s -> u <_ 1 )' % au)
    x0 = closed(w, au, '0xr', '0 e. RR*'); x1 = closed(w, au, '1xr', '1 e. RR*')
    p1 = w.s([x0, x1], 'jca', '( %s -> ( 0 e. RR* /\\ 1 e. RR* ) )' % au)
    l0 = closed(w, au, '0le0', '0 <_ 0')
    p2 = w.s([l0, u1], 'jca', '( %s -> ( 0 <_ 0 /\\ u <_ 1 ) )' % au)
    ss = w.s([p1, p2, w.inst('ioossioo')], 'syl2anc', '( %s -> ( 0 (,) u ) C_ ( 0 (,) 1 ) )' % au)
    sb = w.s([], 'fveq2', '( y = s -> ( H ` y ) = ( H ` s ) )')
    eqi = w.s([], 'eqid', '%s = %s' % (HR, HR))
    vx = w.s([], 'fvex', '( H ` s ) e. _V')
    fv = w.s([sb, eqi, vx], 'fvmpt', '( s e. ( 0 (,) 1 ) -> ( %s ` s ) = ( H ` s ) )' % HR)
    A2 = '( %s /\\ s e. ( 0 (,) u ) )' % au
    ss2 = w.s([ss], 'adantr', '( %s -> ( 0 (,) u ) C_ ( 0 (,) 1 ) )' % A2)
    sr = w.s([], 'simpr', '( %s -> s e. ( 0 (,) u ) )' % A2)
    sin = w.s([ss2, sr], 'sseldd', '( %s -> s e. ( 0 (,) 1 ) )' % A2)
    e1 = w.s([sin, fv], 'syl', '( %s -> ( %s ` s ) = ( H ` s ) )' % (A2, HR))
    e2 = w.s([e1], 'eqcomd', '( %s -> ( H ` s ) = ( %s ` s ) )' % (A2, HR))
    ig = w.s([e2], 'itgeq2dv', '( %s -> S. ( 0 (,) u ) ( H ` s ) _d s = S. ( 0 (,) u ) ( %s ` s ) _d s )' % (au, HR))
    return w.s([ig], 'mpteq2ia', '%s = %s' % (GDEF, GDEFR))


def hrsteps(w):
    """steps (id, H : ( 0 [,] 1 ) --> CC, HR e. ( ( 0 (,) 1 ) -cn-> CC ), HR e. L^1)
    under the antecedent HCN"""
    h = w.s([], 'id', '( %s -> %s )' % (HCN, HCN))
    ff = w.s([h, w.inst('cncff')], 'syl', '( %s -> H : ( 0 [,] 1 ) --> CC )' % HCN)
    ss = closed(w, HCN, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
    res = w.s([ff, ss], 'feqresmpt', '( %s -> ( H |` ( 0 (,) 1 ) ) = %s )' % (HCN, HR))
    rc = w.s([ss, h, w.inst('rescncf')], 'sylc', '( %s -> ( H |` ( 0 (,) 1 ) ) e. ( ( 0 (,) 1 ) -cn-> CC ) )' % HCN)
    hrcn = w.s([res, rc], 'eqeltrrd', '( %s -> %s e. ( ( 0 (,) 1 ) -cn-> CC ) )' % (HCN, HR))
    r0 = w.s([], '0red', '( %s -> 0 e. RR )' % HCN); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % HCN)
    ib = w.s([r0, r1, h, w.inst('cniccibl')], 'syl3anc', '( %s -> H e. L^1 )' % HCN)
    hm = w.s([ff], 'feqmptd', '( %s -> H = %s )' % (HCN, HI))
    ibi = w.s([hm, ib], 'eqeltrrd', '( %s -> %s e. L^1 )' % (HCN, HI))
    mb = closed(w, HCN, 'ioombl', '( 0 (,) 1 ) e. dom vol')
    A2 = '( %s /\\ y e. ( 0 [,] 1 ) )' % HCN
    ff2 = w.s([ff], 'adantr', '( %s -> H : ( 0 [,] 1 ) --> CC )' % A2)
    yy = w.s([], 'simpr', '( %s -> y e. ( 0 [,] 1 ) )' % A2)
    fv = w.s([ff2, yy], 'ffvelcdmd', '( %s -> ( H ` y ) e. CC )' % A2)
    hribl = w.s([ss, mb, fv, ibi], 'iblss', '( %s -> %s e. L^1 )' % (HCN, HR))
    return h, ff, hrcn, hribl, r0, r1


# ---- ftc1icc
w = W('ftc1icc', 'The first fundamental theorem of calculus on the closed unit interval: the derivative of the indefinite integral of a continuous function is the function, on the open interval.')
w.s([], 'ftc1icc.g', 'G = %s' % GDEF, name='h1')
h, ff, hrcn, hribl, r0, r1 = hrsteps(w)
g1 = grewrite(w)
g2 = w.s(['1', g1], 'eqtri', 'G = %s' % GDEFR)
le = w.s([], '0le1', '0 <_ 1'); led = w.s([le], 'a1i', '( %s -> 0 <_ 1 )' % HCN)
w.qed([g2, r0, r1, led, hrcn, hribl], 'ftc1cn', '( %s -> ( RR _D G ) = %s )' % (HCN, HR)); run(w)

# ---- ftc1icccn
w = W('ftc1icccn', 'The indefinite integral of a function continuous on the closed unit interval is continuous on the closed unit interval.')
w.s([], 'ftc1icccn.g', 'G = %s' % GDEF, name='h1')
h, ff, hrcn, hribl, r0, r1 = hrsteps(w)
g1 = grewrite(w)
g2 = w.s(['1', g1], 'eqtri', 'G = %s' % GDEFR)
le = w.s([], '0le1', '0 <_ 1'); led = w.s([le], 'a1i', '( %s -> 0 <_ 1 )' % HCN)
si = w.s([], 'ssidd', '( %s -> ( 0 (,) 1 ) C_ ( 0 (,) 1 ) )' % HCN)
sr = closed(w, HCN, 'ioossre', '( 0 (,) 1 ) C_ RR')
hrf = w.s([hrcn, w.inst('cncff')], 'syl', '( %s -> %s : ( 0 (,) 1 ) --> CC )' % (HCN, HR))
w.qed([g2, r0, r1, led, si, sr, hribl, hrf], 'ftc1a', '( %s -> G e. ( ( 0 [,] 1 ) -cn-> CC ) )' % HCN); run(w)

# ---- ftc1iccntr
w = W('ftc1iccntr', 'The derivative of the indefinite integral of a continuous function, as a mapping on the open unit interval.')
w.s([], 'ftc1iccntr.g', 'G = %s' % GDEF, name='h1')
h = w.s([], 'id', '( %s -> %s )' % (HCN, HCN))
d1 = w.s(['1'], 'ftc1icc', '( %s -> ( RR _D G ) = %s )' % (HCN, HR))
gc = w.s(['1'], 'ftc1icccn', '( %s -> G e. ( ( 0 [,] 1 ) -cn-> CC ) )' % HCN)
gf = w.s([gc, w.inst('cncff')], 'syl', '( %s -> G : ( 0 [,] 1 ) --> CC )' % HCN)
gm = w.s([gf], 'feqmptd', '( %s -> G = ( y e. ( 0 [,] 1 ) |-> ( G ` y ) ) )' % HCN)
gd = w.s([gm], 'oveq2d', '( %s -> ( RR _D G ) = ( RR _D ( y e. ( 0 [,] 1 ) |-> ( G ` y ) ) ) )' % HCN)
rc = closed(w, HCN, 'ax-resscn', 'RR C_ CC')
us = closed(w, HCN, 'unitssre', '( 0 [,] 1 ) C_ RR')
A2 = '( %s /\\ y e. ( 0 [,] 1 ) )' % HCN
gf2 = w.s([gf], 'adantr', '( %s -> G : ( 0 [,] 1 ) --> CC )' % A2)
yy = w.s([], 'simpr', '( %s -> y e. ( 0 [,] 1 ) )' % A2)
gv = w.s([gf2, yy], 'ffvelcdmd', '( %s -> ( G ` y ) e. CC )' % A2)
ej = w.s([], 'eqid', '%s = %s' % (JR, JR)); ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
nt = closed(w, HCN, 'unitntr', '( ( int ` %s ) ` ( 0 [,] 1 ) ) = ( 0 (,) 1 )' % JR)
ntr = w.s([rc, us, gv, ej, ek, nt], 'dvmptntr', '( %s -> ( RR _D ( y e. ( 0 [,] 1 ) |-> ( G ` y ) ) ) = ( RR _D ( y e. ( 0 (,) 1 ) |-> ( G ` y ) ) ) )' % HCN)
e1 = w.s([gd, ntr], 'eqtrd', '( %s -> ( RR _D G ) = ( RR _D ( y e. ( 0 (,) 1 ) |-> ( G ` y ) ) ) )' % HCN)
w.qed([e1, d1], 'eqtr3d', '( %s -> ( RR _D ( y e. ( 0 (,) 1 ) |-> ( G ` y ) ) ) = %s )' % (HCN, HR)); run(w)
