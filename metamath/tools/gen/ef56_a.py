"""Sortie EF56: E1 ( 1 ) = 1 (ef5e11), etaFun_eq_mul (ef5em)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import lin
lin.FASTPATH = True
from zc1_c import u1base

CX1 = '( a e. NN |-> ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` a ) ) )' % U1
PRN1 = '( n e. NN |-> if ( ( n gcd 1 ) = 1 , 1 , 0 ) )'


def gen_e11():
    w = W('ef5e11', 'The value of ` E1 = ( s - 1 ) zeta ( s ) ` at ` 1 ` is ` 1 ` (the residue of ` zeta ` ; ~ zl1e1 , ~ zl1prn , ~ phi1 ).')
    A0 = '1 e. NN'
    one = w.s([], '1nn', '1 e. NN')
    ub = u1base(w, A0)
    nx = w.s([w.s([], 'id', '( 1 e. NN -> 1 e. NN )'), ub], 'jca', '( 1 e. NN -> ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) )' % U1)
    e1 = w.s([nx, w.inst('zl1e1')], 'syl', '( 1 e. NN -> ( %s ` 1 ) = if ( %s = %s , ( ( phi ` 1 ) / 1 ) , 0 ) )' % (E1, CX1, PRN1))
    pr = w.s([nx, w.inst('zl1prn')], 'syl', '( 1 e. NN -> ( %s = %s <-> %s = %s ) )' % (CX1, PRN1, U1, U1))
    tr = w.s([w.s([], 'eqidd', '( 1 e. NN -> %s = %s )' % (U1, U1)), pr], 'mpbird', '( 1 e. NN -> %s = %s )' % (CX1, PRN1))
    it = w.s([tr], 'iftrued', '( 1 e. NN -> if ( %s = %s , ( ( phi ` 1 ) / 1 ) , 0 ) = ( ( phi ` 1 ) / 1 ) )' % (CX1, PRN1))
    p1 = w.s([w.s([w.s([], 'phi1', '( phi ` 1 ) = 1')], 'oveq1i', '( ( phi ` 1 ) / 1 ) = ( 1 / 1 )'), w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'eqtri', '( ( phi ` 1 ) / 1 ) = 1')
    fin = w.s([w.s([e1, it], 'eqtrd', '( 1 e. NN -> ( %s ` 1 ) = ( ( phi ` 1 ) / 1 ) )' % E1), w.s([p1], 'a1i', '( 1 e. NN -> ( ( phi ` 1 ) / 1 ) = 1 )')], 'eqtrd', '( 1 e. NN -> ( %s ` 1 ) = 1 )' % E1)
    w.qed([one, fin], 'ax-mp', S['ef5e11'])
    return run8(w)


def gen_em():
    w = W('ef5em', 'Lean ` etaFun_eq_mul ` : off ` s = 1 ` in the right half-plane, ` eta ( s ) = g ( s ) zeta ( s ) ` with ` zeta ( s ) = E1 ( s ) / ( s - 1 ) ` ( ~ etarel ).')
    A0 = ante_of(S['ef5em'])[0]
    c = Ctx(w, A0)
    sh = c.g('S e. %s' % HP0); s1 = c.g('S =/= 1')
    sc, _ = hp_facts(w, A0, sh, 'S')
    er = c([sh, w.inst('etarel')], 'syl', tsub(stmt('etarel'), {}).split(' -> ', 1)[1][:-2])
    ec = fcc(w, A0, hol_eta(w, A0), ETA, HP0, 'S', sh)
    gc = fcc(w, A0, hol_gf(w, A0), GF, HP0, 'S', sh)
    e1c = fcc(w, A0, hol_e1(w, A0), E1, HP0, 'S', sh)
    ET, GS, ES = '( %s ` S )' % ETA, '( %s ` S )' % GF, '( %s ` S )' % E1
    smc = c([sc, c([], '1cnd', '1 e. CC')], 'subcld', '( S - 1 ) e. CC')
    smn = c([sc, c([], '1cnd', '1 e. CC'), s1], 'subne0d', '( S - 1 ) =/= 0')
    d1 = c([ec, smc, smn], 'divcan3d', '( ( ( S - 1 ) x. %s ) / ( S - 1 ) ) = %s' % (ET, ET))
    d2 = c([er], 'oveq1d', '( ( ( S - 1 ) x. %s ) / ( S - 1 ) ) = ( ( %s x. %s ) / ( S - 1 ) )' % (ET, GS, ES))
    d3 = c([gc, e1c, smc, smn], 'divassd', '( ( %s x. %s ) / ( S - 1 ) ) = ( %s x. ( %s / ( S - 1 ) ) )' % (GS, ES, GS, ES))
    d4 = c([c([d1], 'eqcomd', '%s = ( ( ( S - 1 ) x. %s ) / ( S - 1 ) )' % (ET, ET)), c([d2, d3], 'eqtrd', '( ( ( S - 1 ) x. %s ) / ( S - 1 ) ) = ( %s x. ( %s / ( S - 1 ) ) )' % (ET, GS, ES))],
           'eqtrd', '%s = ( %s x. ( %s / ( S - 1 ) ) )' % (ET, GS, ES))
    w.qed([d4], 'idi', S['ef5em'])
    return run8(w)


GC = '( z e. CC |-> ( 1 - ( 2 ^c ( 1 - z ) ) ) )'


def dv_gc(w, A0):
    """( A0 -> ( CC _D GC ) = ( z e. CC |-> DV ) ), from ZC1's gfhol; returns (step, DV)"""
    from cl import lift
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    Az = '( %s /\\ z e. CC )' % A0
    Ay = '( %s /\\ y e. CC )' % A0
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    sy = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ay, f))
    cc = s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', 'CC e. { RR , CC }')
    one = s([], '1cnd', '1 e. CC')
    d1 = s([cc, one], 'dvmptc', '( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 )')
    d2 = s([cc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    zc = sz([], 'simpr', 'z e. CC')
    one_z = sz([], '1cnd', '1 e. CC'); zero_z = sz([], '0cnd', '0 e. CC')
    dA = s([cc, one_z, zero_z, d1, zc, one_z, d2], 'dvmptsub', '( CC _D ( z e. CC |-> ( 1 - z ) ) ) = ( z e. CC |-> ( 0 - 1 ) )')
    two = numst(w, A0, '2', 'RR+')
    dC0 = s([two, w.inst('dvcxp2')], 'syl', '( CC _D ( y e. CC |-> ( 2 ^c y ) ) ) = ( y e. CC |-> ( ( log ` 2 ) x. ( 2 ^c y ) ) )')
    omz = sz([one_z, zc], 'subcld', '( 1 - z ) e. CC')
    m1 = sz([zero_z, one_z], 'subcld', '( 0 - 1 ) e. CC')
    yc = sy([], 'simpr', 'y e. CC')
    cy = sy([sy([], '2cnd', '2 e. CC'), yc], 'cxpcld', '( 2 ^c y ) e. CC')
    l2c = sy([sy([lift(w, two, Ay)], 'relogcld', '( log ` 2 ) e. RR')], 'recnd', '( log ` 2 ) e. CC')
    dy = sy([l2c, cy], 'mulcld', '( ( log ` 2 ) x. ( 2 ^c y ) ) e. CC')
    e = w.s([], 'oveq2', '( y = ( 1 - z ) -> ( 2 ^c y ) = ( 2 ^c ( 1 - z ) ) )')
    f = w.s([e], 'oveq2d', '( y = ( 1 - z ) -> ( ( log ` 2 ) x. ( 2 ^c y ) ) = ( ( log ` 2 ) x. ( 2 ^c ( 1 - z ) ) ) )')
    F_ = '( ( log ` 2 ) x. ( 2 ^c ( 1 - z ) ) )'
    dE = s([cc, cc, omz, m1, cy, dy, dA, dC0, e, f], 'dvmptco', '( CC _D ( z e. CC |-> ( 2 ^c ( 1 - z ) ) ) ) = ( z e. CC |-> ( %s x. ( 0 - 1 ) ) )' % F_)
    ez = sz([sz([], '2cnd', '2 e. CC'), omz], 'cxpcld', '( 2 ^c ( 1 - z ) ) e. CC')
    fz = sz([sz([lift(w, s([two], 'relogcld', '( log ` 2 ) e. RR'), Az)], 'recnd', '( log ` 2 ) e. CC'), ez], 'mulcld', '%s e. CC' % F_)
    fm = sz([fz, m1], 'mulcld', '( %s x. ( 0 - 1 ) ) e. CC' % F_)
    DV = '( 0 - ( %s x. ( 0 - 1 ) ) )' % F_
    dG = s([cc, one_z, zero_z, d1, ez, fm, dE], 'dvmptsub', '( CC _D %s ) = ( z e. CC |-> %s )' % (GC, DV))
    gv = sz([one_z, ez], 'subcld', '( 1 - ( 2 ^c ( 1 - z ) ) ) e. CC')
    dvv = sz([zero_z, fm], 'subcld', '%s e. CC' % DV)
    return dG, DV, cc, gv, dvv


def gen_gd():
    from cl import lift
    import congr as _cg
    w = W('ef5gd', 'Lean ` deriv_gFun ` : the derivative of ` g ( s ) = 1 - 2 ^ ( 1 - s ) ` is ` log 2 . 2 ^ ( 1 - s ) ` ( ~ dvcxp2 , ~ dvmptco , ~ dvmptres ).')
    A0 = 'S e. %s' % HP0
    c = Ctx(w, A0)
    sh = c([], 'id', A0)
    dG, DV, cc, gv, dvv = dv_gc(w, A0)
    JCC = '( ( TopOpen ` CCfld ) |`t CC )'
    TOP = '( TopOpen ` CCfld )'
    ej = w.s([], 'eqid', '%s = %s' % (JCC, JCC)); ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ss = c([c([], 'cnvimass', "( `' Re \" ( 0 (,) +oo ) ) C_ dom Re"), c.a1(w.s([], 'ref', 'Re : CC --> RR'), 'Re : CC --> RR')], 'x', 'x') if False else None
    hpss = c.a1(w.s([], 'hpss' if False else 'x', 'x'), 'x') if False else None
    sub = c([], 'hpss' if False else 'x', 'x') if False else None
    ssc = c.a1(w.s([w.s([], 'cnvimass', "( `' Re \" ( 0 (,) +oo ) ) C_ dom Re"), w.s([w.s([], 'ref', 'Re : CC --> RR')], 'fdmi', 'dom Re = CC')], 'sseqtri', '%s C_ CC' % HP0), '%s C_ CC' % HP0)
    opn = c.a1(w.s([w.s([], 'hpopn', '%s e. %s' % (HP0, TOP)), w.s([], 'cnrestid', '%s = %s' % (JCC, TOP))], 'eleqtrri', '%s e. %s' % (HP0, JCC)), '%s e. %s' % (HP0, JCC))
    dr = c([cc, gv, dvv, dG, ssc, ej, ek, opn], 'dvmptres', '( CC _D ( z e. %s |-> ( 1 - ( 2 ^c ( 1 - z ) ) ) ) ) = ( z e. %s |-> %s )' % (HP0, HP0, DV))
    V = tsub(DV, {'z': 'S'})
    sc, _ = hp_facts(w, A0, sh, 'S')
    Asz = '( %s /\\ z = S )' % A0
    fv = c([c([], 'eqidd', '( z e. %s |-> %s ) = ( z e. %s |-> %s )' % (HP0, DV, HP0, DV)) if False else None], 'x', 'x') if False else None
    vv, _ = _cg.mptval(w, A0, 'z', HP0, DV, 'S', sh, exs=c([w.s([], 'ovex', '%s e. _V' % V)], 'a1i', '%s e. _V' % V) if False else c.a1(w.s([], 'ovex', '%s e. _V' % V), '%s e. _V' % V), gen=w.g)
    dv = c([c([dr], 'fveq1d', '( ( CC _D %s ) ` S ) = ( ( z e. %s |-> %s ) ` S )' % (GF, HP0, DV)), vv], 'eqtrd', '( ( CC _D %s ) ` S ) = %s' % (GF, V))
    two = numst(w, A0, '2', 'RR+')
    l2 = c([c([two], 'relogcld', '( log ` 2 ) e. RR')], 'recnd', '( log ` 2 ) e. CC')
    pw = c([c([], '2cnd', '2 e. CC'), c([c([], '1cnd', '1 e. CC'), sc], 'subcld', '( 1 - S ) e. CC')], 'cxpcld', '( 2 ^c ( 1 - S ) ) e. CC')
    from cl import Closure
    cl = Closure(w, A0, {'( log ` 2 )': ('CC', l2), '( 2 ^c ( 1 - S ) )': ('CC', pw)})
    cl.atom('( log ` 2 )'); cl.atom('( 2 ^c ( 1 - S ) )')
    rq = ringeq(w, A0, V, '( ( log ` 2 ) x. ( 2 ^c ( 1 - S ) ) )', cl)
    w.qed([dv, rq], 'eqtrd', S['ef5gd'])
    return run8(w)


def gen_g0():
    from cl import lift, Closure
    from zc1_f import gval
    w = W('ef5g0', 'Lean ` gFun_zero_imp ` (as an equivalence): ` g ( s ) = 1 - 2 ^ ( 1 - s ) ` vanishes exactly at ` s = 1 + 2 pi i n / log 2 ` , ` n e. ZZ ` ( ~ efeq1 ).')
    A0 = 'S e. %s' % HP0
    c = Ctx(w, A0)
    sh = c([], 'id', A0)
    sc, _ = hp_facts(w, A0, sh, 'S')
    L = '( log ` 2 )'
    D = '( _i x. ( 2 x. _pi ) )'
    two = numst(w, A0, '2', 'RR+')
    lr = c([two], 'relogcld', '%s e. RR' % L)
    lc = c([lr], 'recnd', '%s e. CC' % L)
    lp = c([c([numst(w, A0, '2', 'RR'), numst(w, A0, '1', 'RR') if False else lin8(w, A0, [], '1 < 2', {})], 'x', 'x') if False else None], 'x', 'x') if False else None
    lpos = c.a1(w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2')], 'loggt0' if False else 'x', 'x'), 'x') if False else None
    lrp = c([numst(w, A0, '2', 'RR'), c.a1(w.s([], '1lt2', '1 < 2'), '1 < 2')], 'rplogcld', '%s e. RR+' % L)
    ln0 = c([lrp], 'rpne0d', '%s =/= 0' % L)
    dc = c.a1(w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([w.s([], '2cn', '2 e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( 2 x. _pi ) e. CC')], 'mulcli', '%s e. CC' % D), '%s e. CC' % D)
    dn0 = c.a1(w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([w.s([], '2cn', '2 e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( 2 x. _pi ) e. CC'), w.s([], 'ine0', '_i =/= 0'),
                    w.s([w.s([], '2cn', '2 e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], '2ne0', '2 =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( 2 x. _pi ) =/= 0')], 'mulne0i', '%s =/= 0' % D), '%s =/= 0' % D)
    SM = '( S - 1 )'
    smc = c([sc, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % SM)
    SL = '( %s x. %s )' % (SM, L)
    slc = c([smc, lc], 'mulcld', '%s e. CC' % SL)
    Q = '( %s / %s )' % (SL, D)
    qc = c([slc, dc, dn0], 'divcld', '%s e. CC' % Q)
    # per n
    An = '( %s /\\ n e. ZZ )' % A0
    cn = Ctx(w, An)
    Ln = lambda st: lift(w, st, An)
    nc = cn([cn([], 'simpr', 'n e. ZZ')], 'zcnd', 'n e. CC')
    TN = '( 2 x. ( _pi x. n ) )'
    tnc = cn([cn([], '2cnd', '2 e. CC'), cn([cn.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC'), nc], 'mulcld', '( _pi x. n ) e. CC')], 'mulcld', '%s e. CC' % TN)
    IC = '( _i x. ( %s / %s ) )' % (TN, L)
    icc = cn([cn.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), cn([tnc, Ln(lc), Ln(ln0)], 'divcld', '( %s / %s ) e. CC' % (TN, L))], 'mulcld', '%s e. CC' % IC)
    GZ = GFZ('n')
    b1 = cn([Ln(sc), cn([], '1cnd', '1 e. CC'), icc, w.inst('subadd')], 'syl3anc', '( ( %s = %s ) <-> ( %s = S ) )' % (SM, IC, GZ) if False else '( %s = %s <-> %s = S )' % (SM, IC, GZ))
    b1b = cn([b1, cn([], 'eqcom', '( %s = S <-> S = %s )' % (GZ, GZ)) if False else cn.a1(w.s([], 'eqcom', '( %s = S <-> S = %s )' % (GZ, GZ)), '( %s = S <-> S = %s )' % (GZ, GZ))], 'bitrd', '( %s = %s <-> S = %s )' % (SM, IC, GZ))
    ND = '( n x. %s )' % D
    ndc = cn([nc, Ln(dc)], 'mulcld', '%s e. CC' % ND)
    ITN = '( _i x. %s )' % TN
    e1 = cn([cn.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), tnc, Ln(lc), Ln(ln0)], 'divassd', '( %s / %s ) = %s' % (ITN, L, IC))
    cl = Closure(w, An, {'n': ('CC', nc), '_pi': ('CC', cn.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')), '_i': ('CC', cn.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'))})
    for k in ('n', '_pi', '_i'):
        cl.atom(k)
    e2 = ringeq(w, An, ITN, ND, cl)
    e3 = cn([cn([e1], 'eqcomd', '%s = ( %s / %s )' % (IC, ITN, L)), cn([e2], 'oveq1d', '( %s / %s ) = ( %s / %s )' % (ITN, L, ND, L))], 'eqtrd', '%s = ( %s / %s )' % (IC, ND, L))
    b2 = cn([e3], 'eqeq2d', '( %s = %s <-> %s = ( %s / %s ) )' % (SM, IC, SM, ND, L))
    b3 = cn([cn([ndc, Ln(smc), Ln(lc), Ln(ln0)], 'jca' if False else 'x', 'x') if False else None], 'x', 'x') if False else None
    dm = cn([ndc, Ln(smc), cn([Ln(lc), Ln(ln0)], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (L, L)), w.inst('divmul3')], 'syl3anc', '( ( %s / %s ) = %s <-> %s = ( %s x. %s ) )' % (ND, L, SM, ND, SM, L))
    ec = cn.a1(w.s([], 'eqcom', '( %s = ( %s / %s ) <-> ( %s / %s ) = %s )' % (SM, ND, L, ND, L, SM)), '( %s = ( %s / %s ) <-> ( %s / %s ) = %s )' % (SM, ND, L, ND, L, SM))
    dm2 = cn([Ln(slc), nc, cn([Ln(dc), Ln(dn0)], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (D, D)), w.inst('divmul3')], 'syl3anc', '( %s = n <-> %s = %s )' % (Q, SL, ND))
    ec2 = cn.a1(w.s([], 'eqcom', '( %s = %s <-> %s = %s )' % (ND, SL, SL, ND)), '( %s = %s <-> %s = %s )' % (ND, SL, SL, ND))
    ec3 = cn.a1(w.s([], 'eqcom', '( %s = n <-> n = %s )' % (Q, Q)), '( %s = n <-> n = %s )' % (Q, Q))
    ch = cn([cn([b1b], 'bicomd', '( S = %s <-> %s = %s )' % (GZ, SM, IC)), b2], 'bitrd', '( S = %s <-> %s = ( %s / %s ) )' % (GZ, SM, ND, L))
    ch = cn([ch, ec], 'bitrd', '( S = %s <-> ( %s / %s ) = %s )' % (GZ, ND, L, SM))
    ch = cn([ch, dm], 'bitrd', '( S = %s <-> %s = %s )' % (GZ, ND, SL))
    ch = cn([ch, ec2], 'bitrd', '( S = %s <-> %s = %s )' % (GZ, SL, ND))
    ch = cn([ch, cn([dm2], 'bicomd', '( %s = %s <-> %s = n )' % (SL, ND, Q))], 'bitrd', '( S = %s <-> %s = n )' % (GZ, Q))
    ch = cn([ch, ec3], 'bitrd', '( S = %s <-> n = %s )' % (GZ, Q))
    rx = c([ch], 'rexbidva', '( E. n e. ZZ S = %s <-> E. n e. ZZ n = %s )' % (GZ, Q))
    rs = c.a1(w.s([], 'risset', '( %s e. ZZ <-> E. n e. ZZ n = %s )' % (Q, Q)), '( %s e. ZZ <-> E. n e. ZZ n = %s )' % (Q, Q))
    right = c([rx, c([rs], 'bicomd', '( E. n e. ZZ n = %s <-> %s e. ZZ )' % (Q, Q))], 'bitrd', '( E. n e. ZZ S = %s <-> %s e. ZZ )' % (GZ, Q))
    # left side
    fv, VAL = gval(w, A0, sh, 'S')
    OM = '( 1 - S )'
    omc = c([c([], '1cnd', '1 e. CC'), sc], 'subcld', '%s e. CC' % OM)
    pw = c([c([], '2cnd', '2 e. CC'), omc], 'cxpcld', '( 2 ^c %s ) e. CC' % OM)
    g1 = c([fv], 'eqeq1d', '( ( %s ` S ) = 0 <-> %s = 0 )' % (GF, VAL))
    g2 = c([c([], '1cnd', '1 e. CC'), pw, w.inst('subeq0')], 'syl2anc', '( %s = 0 <-> 1 = ( 2 ^c %s ) )' % (VAL, OM))
    g3 = c.a1(w.s([], 'eqcom', '( 1 = ( 2 ^c %s ) <-> ( 2 ^c %s ) = 1 )' % (OM, OM)), '( 1 = ( 2 ^c %s ) <-> ( 2 ^c %s ) = 1 )' % (OM, OM))
    W_ = '( %s x. %s )' % (OM, L)
    ce = c([c([], '2cnd', '2 e. CC'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0'), omc], 'cxpefd', '( 2 ^c %s ) = ( exp ` %s )' % (OM, W_))
    g4 = c([ce], 'eqeq1d', '( ( 2 ^c %s ) = 1 <-> ( exp ` %s ) = 1 )' % (OM, W_))
    wc = c([omc, lc], 'mulcld', '%s e. CC' % W_)
    g5 = c([wc, w.inst('efeq1')], 'syl', '( ( exp ` %s ) = 1 <-> ( %s / %s ) e. ZZ )' % (W_, W_, D))
    # W / D = -u Q
    cl0 = Closure(w, A0, {'S': ('CC', sc), L: ('CC', lc)})
    cl0.atom('S'); cl0.atom(L)
    wq = ringeq(w, A0, W_, '-u %s' % SL, cl0)
    dq = c([c([wq], 'oveq1d', '( %s / %s ) = ( -u %s / %s )' % (W_, D, SL, D)), c([c([slc, dc, dn0], 'divnegd', '-u %s = ( -u %s / %s )' % (Q, SL, D))], 'eqcomd', '( -u %s / %s ) = -u %s' % (SL, D, Q))],
           'eqtrd', '( %s / %s ) = -u %s' % (W_, D, Q))
    g6 = c([dq], 'eleq1d', '( ( %s / %s ) e. ZZ <-> -u %s e. ZZ )' % (W_, D, Q))
    g7 = c([qc, w.inst('znegclb')], 'syl', '( %s e. ZZ <-> -u %s e. ZZ )' % (Q, Q))
    left = c([g1, g2], 'bitrd', '( ( %s ` S ) = 0 <-> 1 = ( 2 ^c %s ) )' % (GF, OM))
    for st, f in ((g3, '( 2 ^c %s ) = 1' % OM), (g4, '( exp ` %s ) = 1' % W_), (g5, '( %s / %s ) e. ZZ' % (W_, D)), (g6, '-u %s e. ZZ' % Q),
                  (c([g7], 'bicomd', '( -u %s e. ZZ <-> %s e. ZZ )' % (Q, Q)), '%s e. ZZ' % Q)):
        left = c([left, st], 'bitrd', '( ( %s ` S ) = 0 <-> %s )' % (GF, f))
    fin = c([left, c([right], 'bicomd', '( %s e. ZZ <-> E. n e. ZZ S = %s )' % (Q, GZ))], 'bitrd', '( ( %s ` S ) = 0 <-> E. n e. ZZ S = %s )' % (GF, GZ))
    w.qed([fin], 'idi', S['ef5g0'])
    return run8(w)


GENS = {'ef5e11': gen_e11, 'ef5em': gen_em, 'ef5gd': gen_gd, 'ef5g0': gen_g0}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
