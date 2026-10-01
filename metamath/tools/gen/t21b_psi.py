"""Sortie T21b: t21psi (psiAP_sub_le), t21tha (thetaAP_sub_le)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from ef3lib import ringeq
import cl as _cl
import t21b_ps

DBN = '( Base ` ( DChr ` N ) )'
LN = '( ZRHom ` ( Z/nZ ` N ) )'
ZN = '( Z/nZ ` N )'
CXb = '( x ` ( %s ` b ) )' % LN
PC = '( x ( psiChar ` N ) Y )'
IFx = 'if ( x = %s , Y , 0 )' % U0
EX_ = '( N DChrLF x )'
SCx = SC(EX_, 'T', 'Y')
Dx = '( ( %s - %s ) + %s )' % (PC, IFx, SCx)
Rx = '( %s - %s )' % (Dx, SCx)
Wx = 'sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) )' % (ZF(EX_, HALF, 'T'), WT(EX_))
EFN = EFERR('N', 'T', 'Y')
OML = '( %s x. ( log ` Y ) )' % OM('N')
ERR = '( %s + %s )' % (EFN, OML)
PHI = '( phi ` N )'
R_ = '( 1 / %s )' % PHI
ZTT = ZT('T', 'Y', HALF)
PSIAP = '( A ( psiAP ` N ) Y )'
SUMPC = 'sum_ x e. %s ( %s x. %s )' % (DBN, CXb, PC)
S_R = 'sum_ x e. %s ( %s x. %s )' % (DBN, CXb, Rx)


def gen_psi():
    w = W('t21psi', 'psi in progressions from the explicit formula: for ` A ` a unit mod ` N ` , ` abs ( psi ( Y ; N , A ) - Y / phi ( N ) ) <_ efErr + omega ( N ) log Y + ( 3 / phi ( N ) ) ZT ` (Lean ` psiAP_sub_le ` ; ~ psiaporthu , ~ t21efa , ~ t21nzs , ~ dchrhash ).')
    A0, concl = split_imp(SB['t21psi'])
    u = unpackA(w, A0)
    nn = u['N e. NN']; az = u['A e. ZZ']; ag = u['( A gcd N ) = 1']; yr = u['Y e. RR']; y100 = u['; ; 1 0 0 <_ Y']; tr = u['T e. RR']; t2 = u['2 <_ T']; ny = u['N <_ Y']
    DV = '%s || ( ( A x. b ) - 1 )' % 'N'
    Ab = '( ( %s /\\ b e. ZZ ) /\\ %s )' % (A0, DV)
    s = S_(w, Ab)
    L = lambda st: lift(w, st, Ab)
    bz = s([], 'simplr', 'b e. ZZ'); dv = s([], 'simpr', DV)
    nnb = L(nn); yrb = L(yr)
    y1 = lin.linarith(w, Ab, [L(y100)], '1 <_ Y', leaves={'Y': yrb})
    yp = rp_of(w, Ab, yrb, y1, 'Y')
    eG = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); eZ = w.s([], 'eqid', '%s = %s' % (ZN, ZN)); eD = w.s([], 'eqid', '%s = %s' % (DBN, DBN)); eL = w.s([], 'eqid', '%s = %s' % (LN, LN))
    eU = w.s([], 'eqid', '( Unit ` %s ) = ( Unit ` %s )' % (ZN, ZN)); eO = w.s([], 'eqid', '%s = %s' % (U0, U0))
    dfin = s([nnb, w.s([eG, eD], 'dchrfi', '( N e. NN -> %s e. Fin )' % DBN)], 'syl', '%s e. Fin' % DBN)
    ab_, gi_ = t21b_ps.u0base(w, Ab)
    u0b = s([s([s([nnb, ab_], 'syl', '( DChr ` N ) e. Abel'), w.inst('ablgrp')], 'syl', '( DChr ` N ) e. Grp'), gi_], 'syl', '%s e. %s' % (U0, DBN))
    # per character
    Ax = '( %s /\\ x e. %s )' % (Ab, DBN)
    sx = S_(w, Ax)
    Lx = lambda st: lift(w, st, Ax)
    xin = sx([], 'simpr', 'x e. %s' % DBN)
    chv = ap(w, Ax, [Lx(nnb), xin, Lx(bz)], 'cen2chv', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CXb, CXb))
    cc_ = sx([chv], 'simpld', '%s e. CC' % CXb); c1 = sx([chv], 'simprd', '( abs ` %s ) <_ 1' % CXb)
    pcc = sx([sx([Lx(nnb), xin, Lx(yrb)], '3jca', '( N e. NN /\\ x e. %s /\\ Y e. RR )' % DBN), w.inst('psicharcl')], 'syl', '%s e. CC' % PC)
    ifc = sx([sx([Lx(yrb)], 'recnd', 'Y e. CC'), sx([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFx)
    scc = sc_cc(w, Ax, 'N', 'x', Lx(nnb), xin, Lx(L(tr)), Lx(yrb))
    cl = _cl.Closure(w, Ax, {})
    for k_, st_ in ((PC, pcc), (IFx, ifc), (SCx, scc), (CXb, cc_)):
        cl.leaf(k_, 'CC', st_); cl.atom(k_)
    rq = ringeq(w, Ax, '( %s x. %s )' % (CXb, PC), '( ( %s x. %s ) + ( %s x. %s ) )' % (CXb, IFx, CXb, Rx), cl)
    t_if = sx([cc_, ifc], 'mulcld', '( %s x. %s ) e. CC' % (CXb, IFx))
    dxc = sx([sx([pcc, ifc], 'subcld', '( %s - %s ) e. CC' % (PC, IFx)), scc], 'addcld', '%s e. CC' % Dx)
    rxc = sx([dxc, scc], 'subcld', '%s e. CC' % Rx)
    t_r = sx([cc_, rxc], 'mulcld', '( %s x. %s ) e. CC' % (CXb, Rx))
    SIF = 'sum_ x e. %s ( %s x. %s )' % (DBN, CXb, IFx)
    sp1 = s([rq], 'sumeq2dv', '%s = sum_ x e. %s ( ( %s x. %s ) + ( %s x. %s ) )' % (SUMPC, DBN, CXb, IFx, CXb, Rx))
    sp2 = s([dfin, t_if, t_r], 'fsumadd', 'sum_ x e. %s ( ( %s x. %s ) + ( %s x. %s ) ) = ( %s + %s )' % (DBN, CXb, IFx, CXb, Rx, SIF, S_R))
    # SIF = Y
    Ao = '( %s /\\ x e. ( %s \\ { %s } ) )' % (Ab, DBN, U0)
    so = S_(w, Ao)
    xo = so([so([], 'simpr', 'x e. ( %s \\ { %s } )' % (DBN, U0)), w.inst('eldifi')], 'syl', 'x e. %s' % DBN)
    xne = so([so([so([], 'simpr', 'x e. ( %s \\ { %s } )' % (DBN, U0)), w.inst('eldifn')], 'syl', '-. x e. { %s }' % U0), w.s([], 'velsn', '( x e. { %s } <-> x = %s )' % (U0, U0))], 'x', 'x') if False else None
    xnn = so([so([], 'simpr', 'x e. ( %s \\ { %s } )' % (DBN, U0)), w.inst('eldifn')], 'syl', '-. x e. { %s }' % U0)
    xne = so([xnn, so([w.s([], 'velsn', '( x e. { %s } <-> x = %s )' % (U0, U0))], 'a1i', '( x e. { %s } <-> x = %s )' % (U0, U0))], 'mtbid', '-. x = %s' % U0)
    if0 = so([xne, w.s([], 'iffalse', '( -. x = %s -> %s = 0 )' % (U0, IFx))], 'syl', '%s = 0' % IFx)
    toAx = so([so([], 'simpl', Ab), xo], 'jca', Ax)
    cco = so([toAx, cc_], 'syl', '%s e. CC' % CXb)
    z0 = so([so([if0], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (CXb, IFx, CXb)), so([cco], 'mul01d', '( %s x. 0 ) = 0' % CXb)], 'eqtrd', '( %s x. %s ) = 0' % (CXb, IFx))
    Asn = '( %s /\\ x e. { %s } )' % (Ab, U0)
    ssn = S_(w, Asn)
    xs = ssn([ssn([], 'simpr', 'x e. { %s }' % U0), w.s([], 'velsn', '( x e. { %s } <-> x = %s )' % (U0, U0)) and ssn([w.s([], 'velsn', '( x e. { %s } <-> x = %s )' % (U0, U0))], 'a1i', '( x e. { %s } <-> x = %s )' % (U0, U0))], 'mpbid', 'x = %s' % U0)
    xsb = ssn([xs, lift(w, u0b, Asn)], 'eqeltrd', 'x e. %s' % DBN)
    tsn = ssn([ssn([ssn([], 'simpl', Ab), xsb], 'jca', Ax), t_if], 'syl', '( %s x. %s ) e. CC' % (CXb, IFx))
    snss = s([u0b], 'snssd', '{ %s } C_ %s' % (U0, DBN))
    fss = s([snss, tsn, z0, dfin], 'fsumss', 'sum_ x e. { %s } ( %s x. %s ) = %s' % (U0, CXb, IFx, SIF))
    C0 = '( %s ` ( %s ` b ) )' % (U0, LN)
    IF0 = 'if ( %s = %s , Y , 0 )' % (U0, U0)
    cxe = w.s([w.s([w.s([], 'id', '( x = %s -> x = %s )' % (U0, U0))], 'fveq1d', '( x = %s -> %s = %s )' % (U0, CXb, C0)),
               w.s([w.s([], 'eqeq1', '( x = %s -> ( x = %s <-> %s = %s ) )' % (U0, U0, U0, U0))], 'ifbid', '( x = %s -> %s = %s )' % (U0, IFx, IF0))], 'oveq12d',
              '( x = %s -> ( %s x. %s ) = ( %s x. %s ) )' % (U0, CXb, IFx, C0, IF0))
    it0 = w.s([w.s([], 'eqid', '%s = %s' % (U0, U0)), w.s([], 'iftrue', '( %s = %s -> %s = Y )' % (U0, U0, IF0))], 'ax-mp', '%s = Y' % IF0)
    # C0 = 1: U0 ( L A ) U0 ( L b ) = U0 ( L ( A b ) ) = U0 ( L 1 ) = 1, U0 ( L A ) = 1
    un = w.s([eZ, eU, eL], 'znunit', '( ( N e. NN0 /\\ A e. ZZ ) -> ( ( %s ` A ) e. ( Unit ` %s ) <-> ( A gcd N ) = 1 ) )' % (LN, ZN))
    n0 = s([nnb], 'nnnn0d', 'N e. NN0')
    uA = s([L(ag), s([s([n0, L(az)], 'jca', '( N e. NN0 /\\ A e. ZZ )'), un], 'syl', '( ( %s ` A ) e. ( Unit ` %s ) <-> ( A gcd N ) = 1 )' % (LN, ZN))], 'mpbird', '( %s ` A ) e. ( Unit ` %s )' % (LN, ZN))
    v1A = w.s([eG, eZ, eO, eU, nnb, uA], 'dchr1', '( %s -> ( %s ` ( %s ` A ) ) = 1 )' % (Ab, U0, LN))
    mul = w.s([eG, eZ, eD, eL, u0b, L(az), bz], 'dchrzrhmul', '( %s -> ( %s ` ( %s ` ( A x. b ) ) ) = ( ( %s ` ( %s ` A ) ) x. %s ) )' % (Ab, U0, LN, U0, LN, C0))
    abz = s([L(az), bz], 'zmulcld', '( A x. b ) e. ZZ')
    zd = w.s([eZ, eL], 'zndvds', '( ( N e. NN0 /\\ ( A x. b ) e. ZZ /\\ 1 e. ZZ ) -> ( ( %s ` ( A x. b ) ) = ( %s ` 1 ) <-> N || ( ( A x. b ) - 1 ) ) )' % (LN, LN))
    l1 = s([dv, s([s([n0, abz, s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')], '3jca', '( N e. NN0 /\\ ( A x. b ) e. ZZ /\\ 1 e. ZZ )'), zd], 'syl',
                    '( ( %s ` ( A x. b ) ) = ( %s ` 1 ) <-> N || ( ( A x. b ) - 1 ) )' % (LN, LN))], 'mpbird', '( %s ` ( A x. b ) ) = ( %s ` 1 )' % (LN, LN))
    one1 = w.s([eG, eZ, eD, eL, u0b], 'dchrzrh1', '( %s -> ( %s ` ( %s ` 1 ) ) = 1 )' % (Ab, U0, LN))
    e1 = s([s([s([l1], 'fveq2d', '( %s ` ( %s ` ( A x. b ) ) ) = ( %s ` ( %s ` 1 ) )' % (U0, LN, U0, LN)), one1], 'eqtrd', '( %s ` ( %s ` ( A x. b ) ) ) = 1' % (U0, LN))], 'x', 'x') if False else None
    e1 = s([s([l1], 'fveq2d', '( %s ` ( %s ` ( A x. b ) ) ) = ( %s ` ( %s ` 1 ) )' % (U0, LN, U0, LN)), one1], 'eqtrd', '( %s ` ( %s ` ( A x. b ) ) ) = 1' % (U0, LN))
    e2 = s([s([mul], 'eqcomd', '( ( %s ` ( %s ` A ) ) x. %s ) = ( %s ` ( %s ` ( A x. b ) ) )' % (U0, LN, C0, U0, LN)), e1], 'eqtrd', '( ( %s ` ( %s ` A ) ) x. %s ) = 1' % (U0, LN, C0))
    c0c = w.s([eG, eZ, eD, eL, u0b, bz], 'dchrzrhcl', '( %s -> %s e. CC )' % (Ab, C0))
    e3 = s([s([s([v1A], 'oveq1d', '( ( %s ` ( %s ` A ) ) x. %s ) = ( 1 x. %s )' % (U0, LN, C0, C0)), s([c0c], 'mullidd', '( 1 x. %s ) = %s' % (C0, C0))], 'eqtrd', '( ( %s ` ( %s ` A ) ) x. %s ) = %s' % (U0, LN, C0, C0)), e2], 'eqtr3d', '%s = 1' % C0)
    sv = s([cxe, s([u0b, s([s([c0c, s([s([it0], 'a1i', '%s = Y' % IF0), s([yrb], 'recnd', 'Y e. CC')], 'eqeltrd', '%s e. CC' % IF0)], 'mulcld', '( %s x. %s ) e. CC' % (C0, IF0))], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    yc = s([yrb], 'recnd', 'Y e. CC')
    t0c = s([c0c, s([s([it0], 'a1i', '%s = Y' % IF0), yc], 'eqeltrrd', '%s e. CC' % IF0) if False else s([s([s([it0], 'a1i', '%s = Y' % IF0)], 'eqcomd', 'Y = %s' % IF0), yc], 'x', 'x') if False else None], 'x', 'x') if False else None
    ifc0 = s([s([s([it0], 'a1i', '%s = Y' % IF0)], 'eqcomd', 'Y = %s' % IF0), yc], 'eqeltrrd', '%s e. CC' % IF0) if False else s([yc, s([s([it0], 'a1i', '%s = Y' % IF0)], 'eqcomd', 'Y = %s' % IF0)], 'eqeltrd', '%s e. CC' % IF0) if False else None
    ifc0 = s([s([it0], 'a1i', '%s = Y' % IF0), yc], 'x', 'x') if False else None
    ifc0 = s([s([s([it0], 'a1i', '%s = Y' % IF0)], 'eqcomd', 'Y = %s' % IF0), yc], 'x', 'x') if False else None
    ifc0 = s([yc, s([s([s([it0], 'a1i', '%s = Y' % IF0)], 'eqcomd', 'Y = %s' % IF0)], 'x', 'x') if False else None], 'x', 'x') if False else None
    ifc0 = s([s([s([it0], 'a1i', '%s = Y' % IF0)], 'eqcomd', 'Y = %s' % IF0), yc], 'x', 'x') if False else None
    ifc0 = w.s([s([w.s([it0], 'eqcomi', 'Y = %s' % IF0)], 'a1i', 'Y = %s' % IF0), yc], 'x', 'x') if False else None
    ifc0 = s([yc, s([w.s([it0], 'eqcomi', 'Y = %s' % IF0)], 'a1i', 'Y = %s' % IF0)], 'eqeltrrd', '%s e. CC' % IF0) if False else s([s([w.s([it0], 'eqcomi', 'Y = %s' % IF0)], 'a1i', 'Y = %s' % IF0), yc], 'eqeltrrd', '%s e. CC' % IF0) if False else None
    ifc0 = s([s([it0], 'a1i', '%s = Y' % IF0), yc], 'eqeltrd', 'x') if False else None
    # simplest: IF0 e. CC by ifcld
    ifc0 = s([yc, s([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF0)
    ssum = w.s([cxe], 'sumsn', '( ( %s e. _V /\\ ( %s x. %s ) e. CC ) -> sum_ x e. { %s } ( %s x. %s ) = ( %s x. %s ) )' % (U0, C0, IF0, U0, CXb, IFx, C0, IF0))
    sv = s([s([s([w.s([], 'fvex', '%s e. _V' % U0)], 'a1i', '%s e. _V' % U0), s([c0c, ifc0], 'mulcld', '( %s x. %s ) e. CC' % (C0, IF0))], 'jca', '( %s e. _V /\\ ( %s x. %s ) e. CC )' % (U0, C0, IF0)), ssum], 'syl',
           'sum_ x e. { %s } ( %s x. %s ) = ( %s x. %s )' % (U0, CXb, IFx, C0, IF0))
    vy = s([s([e3, s([it0], 'a1i', '%s = Y' % IF0)], 'oveq12d', '( %s x. %s ) = ( 1 x. Y )' % (C0, IF0)), s([yc], 'mullidd', '( 1 x. Y ) = Y')], 'eqtrd', '( %s x. %s ) = Y' % (C0, IF0))
    sif = s([s([fss], 'eqcomd', '%s = sum_ x e. { %s } ( %s x. %s )' % (SIF, U0, CXb, IFx)), s([sv, vy], 'eqtrd', 'sum_ x e. { %s } ( %s x. %s ) = Y' % (U0, CXb, IFx))], 'eqtrd', '%s = Y' % SIF)
    spc = s([s([sp1, sp2], 'eqtrd', '%s = ( %s + %s )' % (SUMPC, SIF, S_R)), s([sif], 'oveq1d', '( %s + %s ) = ( Y + %s )' % (SIF, S_R, S_R))], 'eqtrd', '%s = ( Y + %s )' % (SUMPC, S_R))
    # per character bound
    efx = ap(w, Ax, [Lx(nnb), xin, Lx(yrb), Lx(L(y100)), Lx(L(tr)), Lx(L(t2)), Lx(L(ny))], 't21efa', '( abs ` %s ) <_ %s' % (Dx, ERR))
    nzx = ap(w, Ax, [Lx(nnb), xin, Lx(L(tr)), Lx(yp)], 't21nzs', '( abs ` %s ) <_ ( 3 x. %s )' % (SCx, Wx))
    a1 = sx([cc_, rxc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CXb, Rx, CXb, Rx))
    arx = sx([rxc], 'abscld', '( abs ` %s ) e. RR' % Rx)
    acr = sx([cc_], 'abscld', '( abs ` %s ) e. RR' % CXb)
    m1 = sx([acr, sx([], '1red', '1 e. RR'), arx, sx([rxc], 'absge0d', '0 <_ ( abs ` %s )' % Rx), c1], 'lemul1ad', '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( 1 x. ( abs ` %s ) )' % (CXb, Rx, Rx))
    m1b = sx([m1, sx([sx([arx], 'recnd', '( abs ` %s ) e. CC' % Rx)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (Rx, Rx))], 'breqtrd', '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( abs ` %s )' % (CXb, Rx, Rx))
    tri = sx([dxc, scc], 'abs2dif2d', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (Rx, Dx, SCx))
    wxr = None
    # Wx real
    fin_, tc_, dd = sc_terms(w, Ax, 'N', 'x', Lx(nnb), xin, Lx(L(tr)), Lx(yrb))
    C2 = dd['C2']
    s2 = S_(w, C2)
    orr = s2([dd['ordn']], 'nnred', '( %s holord q ) e. RR' % EX_)
    import t21alib as _ta
    wr, _, _ = _ta.wt_facts(w, C2, orr, s2([s2([dd['ordn']], 'nnnn0d', '( %s holord q ) e. NN0' % EX_)], 'nn0ge0d', '0 <_ ( %s holord q )' % EX_), dd['qf'])
    yre = s2([lift(w, yp, C2), dd['qf']['re']], 'rpcxpcld', '( Y ^c ( Re ` q ) ) e. RR+')
    wxr = sx([fin_, s2([wr, s2([yre], 'rpred', '( Y ^c ( Re ` q ) ) e. RR')], 'remulcld', '( %s x. ( Y ^c ( Re ` q ) ) ) e. RR' % WT(EX_))], 'fsumrecl', '%s e. RR' % Wx)
    errr = Lx(L(eferr_parts(w, A0, 'N', None, None, None, None, None, None)['er'])) if False else None
    pN = eferr_parts(w, Ab, 'N', s([nnb], 'nnred', 'N e. RR'), s([nnb], 'nnge1d', '1 <_ N'), yrb, y1, L(tr), L(t2))
    omn = s([s([nnb, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OM('N'))
    omlr = s([s([omn], 'nn0red', '%s e. RR' % OM('N')), s([yp], 'relogcld', '( log ` Y ) e. RR')], 'remulcld', '%s e. RR' % OML)
    errr = s([pN['er'], omlr], 'readdcld', '%s e. RR' % ERR)
    w3 = sx([sx([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), wxr], 'remulcld', '( 3 x. %s ) e. RR' % Wx)
    bnd = sx([sx([dxc], 'abscld', '( abs ` %s ) e. RR' % Dx), sx([scc], 'abscld', '( abs ` %s ) e. RR' % SCx), Lx(errr), w3, efx, nzx], 'le2addd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + ( 3 x. %s ) )' % (Dx, SCx, ERR, Wx))
    PB = '( %s + ( 3 x. %s ) )' % (ERR, Wx)
    pbr = sx([Lx(errr), w3], 'readdcld', '%s e. RR' % PB)
    rb = sx([arx, sx([sx([dxc], 'abscld', '( abs ` %s ) e. RR' % Dx), sx([scc], 'abscld', '( abs ` %s ) e. RR' % SCx)], 'readdcld', '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (Dx, SCx)), pbr, tri, bnd], 'letrd', '( abs ` %s ) <_ %s' % (Rx, PB))
    tb = sx([sx([a1, m1b], 'eqbrtrd', '( abs ` ( %s x. %s ) ) <_ ( abs ` %s )' % (CXb, Rx, Rx)), rb], 'x', 'x') if False else None
    trr = sx([t_r], 'abscld', '( abs ` ( %s x. %s ) ) e. RR' % (CXb, Rx))
    tb = sx([trr, arx, pbr, sx([a1, m1b], 'eqbrtrd', '( abs ` ( %s x. %s ) ) <_ ( abs ` %s )' % (CXb, Rx, Rx)), rb], 'letrd', '( abs ` ( %s x. %s ) ) <_ %s' % (CXb, Rx, PB))
    # sums over characters
    fa = s([dfin, t_r], 'fsumabs', '( abs ` %s ) <_ sum_ x e. %s ( abs ` ( %s x. %s ) )' % (S_R, DBN, CXb, Rx))
    fl = s([dfin, trr, pbr, tb], 'fsumle', 'sum_ x e. %s ( abs ` ( %s x. %s ) ) <_ sum_ x e. %s %s' % (DBN, CXb, Rx, DBN, PB))
    fad = s([dfin, Lx(s([errr], 'recnd', '%s e. CC' % ERR)) if False else sx([Lx(errr)], 'recnd', '%s e. CC' % ERR), sx([w3], 'recnd', '( 3 x. %s ) e. CC' % Wx)], 'fsumadd', 'sum_ x e. %s %s = ( sum_ x e. %s %s + sum_ x e. %s ( 3 x. %s ) )' % (DBN, PB, DBN, ERR, DBN, Wx))
    fcs = s([s([dfin, s([errr], 'recnd', '%s e. CC' % ERR)], 'jca', '( %s e. Fin /\\ %s e. CC )' % (DBN, ERR)), w.inst('fsumconst')], 'syl', 'sum_ x e. %s %s = ( ( # ` %s ) x. %s )' % (DBN, ERR, DBN, ERR))
    dh = s([nnb, w.s([eG, eD], 'dchrhash', '( N e. NN -> ( # ` %s ) = %s )' % (DBN, PHI))], 'syl', '( # ` %s ) = %s' % (DBN, PHI))
    fm = s([dfin, s([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC'), sx([wxr], 'recnd', '%s e. CC' % Wx)], 'fsummulc2', '( 3 x. %s ) = sum_ x e. %s ( 3 x. %s )' % (ZTT, DBN, Wx))
    TOT = '( ( %s x. %s ) + ( 3 x. %s ) )' % (PHI, ERR, ZTT)
    tot = s([fad, s([s([fcs, s([dh], 'oveq1d', '( ( # ` %s ) x. %s ) = ( %s x. %s )' % (DBN, ERR, PHI, ERR))], 'eqtrd', 'sum_ x e. %s %s = ( %s x. %s )' % (DBN, ERR, PHI, ERR)),
                                     s([fm], 'eqcomd', 'sum_ x e. %s ( 3 x. %s ) = ( 3 x. %s )' % (DBN, Wx, ZTT))], 'oveq12d', '( sum_ x e. %s %s + sum_ x e. %s ( 3 x. %s ) ) = %s' % (DBN, ERR, DBN, Wx, TOT))], 'eqtrd',
            'sum_ x e. %s %s = %s' % (DBN, PB, TOT))
    ssr = s([s([dfin, t_r], 'fsumcl', '%s e. CC' % S_R)], 'abscld', '( abs ` %s ) e. RR' % S_R)
    sar = s([dfin, trr], 'fsumrecl', 'sum_ x e. %s ( abs ` ( %s x. %s ) ) e. RR' % (DBN, CXb, Rx))
    spr = s([dfin, pbr], 'fsumrecl', 'sum_ x e. %s %s e. RR' % (DBN, PB))
    sb = s([s([ssr, sar, spr, fa, fl], 'letrd', '( abs ` %s ) <_ sum_ x e. %s %s' % (S_R, DBN, PB)), tot], 'breqtrd', '( abs ` %s ) <_ %s' % (S_R, TOT))
    # PSIAP - Y / phi = r S
    phn = s([nnb, w.inst('phicl')], 'syl', '%s e. NN' % PHI)
    php = s([phn], 'nnrpd', '%s e. RR+' % PHI)
    rp_ = s([php], 'rpreccld', '%s e. RR+' % R_)
    rc = s([rp_], 'rpcnd', '%s e. CC' % R_)
    src = s([dfin, t_r], 'fsumcl', '%s e. CC' % S_R)
    EQ = '%s = ( %s x. %s )' % (PSIAP, R_, SUMPC)
    Ae = '( %s /\\ %s )' % (Ab, EQ)
    se = S_(w, Ae)
    Le = lambda st: lift(w, st, Ae)
    pe = se([se([], 'simpr', EQ), Le(s([spc], 'oveq2d', '( %s x. %s ) = ( %s x. ( Y + %s ) )' % (R_, SUMPC, R_, S_R)))], 'eqtrd', '%s = ( %s x. ( Y + %s ) )' % (PSIAP, R_, S_R))
    ydp = se([Le(yc), Le(s([php], 'rpcnd', '%s e. CC' % PHI)), Le(s([php], 'rpne0d', '%s =/= 0' % PHI))], 'divrecd', '( Y / %s ) = ( Y x. %s )' % (PHI, R_))
    cl2 = _cl.Closure(w, Ae, {})
    for k_, st_ in ((R_, Le(rc)), ('Y', Le(yc)), (S_R, Le(src))):
        cl2.leaf(k_, 'CC', st_); cl2.atom(k_)
    rq2 = ringeq(w, Ae, '( ( %s x. ( Y + %s ) ) - ( Y x. %s ) )' % (R_, S_R, R_), '( %s x. %s )' % (R_, S_R), cl2)
    diff = se([se([pe, ydp], 'oveq12d', '( %s - ( Y / %s ) ) = ( ( %s x. ( Y + %s ) ) - ( Y x. %s ) )' % (PSIAP, PHI, R_, S_R, R_)), rq2], 'eqtrd', '( %s - ( Y / %s ) ) = ( %s x. %s )' % (PSIAP, PHI, R_, S_R))
    ab2 = se([Le(rc), Le(src)], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (R_, S_R, R_, S_R))
    ar = se([Le(s([rp_], 'rpred', '%s e. RR' % R_)), Le(s([rp_], 'rpge0d', '0 <_ %s' % R_))], 'absidd', '( abs ` %s ) = %s' % (R_, R_))
    ab3 = se([ab2, se([ar], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (R_, S_R, R_, S_R))], 'eqtrd', '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (R_, S_R, R_, S_R))
    totr = s([s([s([php], 'rpred', '%s e. RR' % PHI), errr], 'remulcld', '( %s x. %s ) e. RR' % (PHI, ERR)), s([s([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'),
               s([dfin, sx([wxr], 'x', 'x') if False else wxr], 'fsumrecl', '%s e. RR' % ZTT)], 'remulcld', '( 3 x. %s ) e. RR' % ZTT)], 'readdcld', '%s e. RR' % TOT)
    mb = se([Le(ssr), Le(totr), Le(s([rp_], 'rpred', '%s e. RR' % R_)), Le(s([rp_], 'rpge0d', '0 <_ %s' % R_)), Le(sb)], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. %s )' % (R_, S_R, R_, TOT))
    cl3 = _cl.Closure(w, Ae, {})
    RHS = ERRS_ = '( %s + ( ( 3 / %s ) x. %s ) )' % (ERR, PHI, ZTT)
    phc = Le(s([php], 'rpcnd', '%s e. CC' % PHI))
    rphi = se([phc, Le(s([php], 'rpne0d', '%s =/= 0' % PHI))], 'recid2d', '( %s x. %s ) = 1' % (R_, PHI))
    t3 = se([se([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC'), phc, Le(s([php], 'rpne0d', '%s =/= 0' % PHI))], 'divrecd', '( 3 / %s ) = ( 3 x. %s )' % (PHI, R_))
    ztc = Le(s([s([dfin, wxr], 'fsumrecl', '%s e. RR' % ZTT)], 'recnd', '%s e. CC' % ZTT))
    ec = Le(s([errr], 'recnd', '%s e. CC' % ERR))
    for k_, st_ in ((R_, Le(rc)), (PHI, phc), (ERR, ec), (ZTT, ztc)):
        cl3.leaf(k_, 'CC', st_); cl3.atom(k_)
    rq3 = ringeq(w, Ae, '( %s x. %s )' % (R_, TOT), '( ( ( %s x. %s ) x. %s ) + ( ( 3 x. %s ) x. %s ) )' % (R_, PHI, ERR, R_, ZTT), cl3)
    rq4 = se([rq3, se([se([rphi], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (R_, PHI, ERR, ERR)), se([se([t3], 'eqcomd', '( 3 x. %s ) = ( 3 / %s )' % (R_, PHI))], 'oveq1d',
                                                                     '( ( 3 x. %s ) x. %s ) = ( ( 3 / %s ) x. %s )' % (R_, ZTT, PHI, ZTT))], 'oveq12d',
                         '( ( ( %s x. %s ) x. %s ) + ( ( 3 x. %s ) x. %s ) ) = ( ( 1 x. %s ) + ( ( 3 / %s ) x. %s ) )' % (R_, PHI, ERR, R_, ZTT, ERR, PHI, ZTT))], 'eqtrd',
              '( %s x. %s ) = ( ( 1 x. %s ) + ( ( 3 / %s ) x. %s ) )' % (R_, TOT, ERR, PHI, ZTT))
    rq5 = se([rq4, se([se([ec], 'mullidd', '( 1 x. %s ) = %s' % (ERR, ERR))], 'oveq1d', '( ( 1 x. %s ) + ( ( 3 / %s ) x. %s ) ) = %s' % (ERR, PHI, ZTT, RHS))], 'eqtrd', '( %s x. %s ) = %s' % (R_, TOT, RHS))
    fin = se([se([se([diff], 'fveq2d', '( abs ` ( %s - ( Y / %s ) ) ) = ( abs ` ( %s x. %s ) )' % (PSIAP, PHI, R_, S_R)), ab3], 'eqtrd', '( abs ` ( %s - ( Y / %s ) ) ) = ( %s x. ( abs ` %s ) )' % (PSIAP, PHI, R_, S_R)),
              se([mb, rq5], 'breqtrd', '( %s x. ( abs ` %s ) ) <_ %s' % (R_, S_R, RHS))], 'eqbrtrd', concl)
    imp = s([fin], 'ex', '( %s -> %s )' % (EQ, concl))
    imp2 = w.s([imp], 'expimpd', '( ( %s /\\ b e. ZZ ) -> ( ( %s /\\ %s ) -> %s ) )' % (A0, DV, EQ, concl))
    rx = w.s([imp2], 'rexlimdva', '( %s -> ( E. b e. ZZ ( %s /\\ %s ) -> %s ) )' % (A0, DV, EQ, concl))
    ex = ap(w, A0, [nn, az, ag, yr], 'psiaporthu', 'E. b e. ZZ ( %s /\\ %s )' % (DV, EQ))
    w.qed([ex, rx], 'mpd', SB['t21psi'])
    return go(w)


if __name__ == '__main__':
    gen_psi()
