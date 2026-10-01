"""Sortie T21a: the sigma grid (t21gridr, t21grid = grid_bound) and its geometric evaluation
(t21ggeo = grid_geom), the zone assembly lemma t21gz."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W


def gen_gridr():
    w = W('t21gridr', 'Pointwise sigma grid: for ` S <_ B < U <_ S + M H ` , ` V >_ 0 ` , ` Y >_ 1 ` , ` V Y ^ B <_ sum_ ( k < M ) [ S + k H <_ B ] V Y ^ ( S + ( k + 1 ) H ) ` : the bucket ` k = floor ( ( B - S ) / H ) ` alone suffices (Lean ` grid_bound ` , its pointwise step).')
    A0 = ante_of(S['t21gridr'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    yr, y1, hp, mn, sr, br, ur, sb, bu, um, vr, v0 = [u[k] for k in ['Y e. RR', '1 <_ Y', 'H e. RR+', 'M e. NN0', 'S e. RR', 'B e. RR', 'U e. RR', 'S <_ B', 'B < U', 'U <_ ( S + ( M x. H ) )', 'V e. RR', '0 <_ V']]
    hr = st([hp], 'rpred', 'H e. RR')
    BS = '( B - S )'; Q = '( %s / H )' % BS; K0 = '( |_ ` %s )' % Q
    bsr = st([br, sr], 'resubcld', '%s e. RR' % BS)
    bs0 = st([sb, st([br, sr], 'subge0d', '( 0 <_ %s <-> S <_ B )' % BS)], 'mpbird', '0 <_ %s' % BS)
    qr = st([bsr, hp], 'rerpdivcld', '%s e. RR' % Q)
    q0 = st([bsr, hp, bs0], 'divge0d', '0 <_ %s' % Q)
    k0 = ap_(w, A0, [qr, q0], 'flge0nn0', '%s e. NN0' % K0)
    k0r = st([k0], 'nn0red', '%s e. RR' % K0)
    kq = ap_(w, A0, [qr], 'flle', '%s <_ %s' % (K0, Q))
    qk = ap_(w, A0, [qr], 'flltp1', '%s < ( %s + 1 )' % (Q, K0))
    KH = '( %s x. H )' % K0
    kh = st([kq, st([k0r, bsr, hp], 'lemuldivd', '( %s <_ %s <-> %s <_ %s )' % (KH, BS, K0, Q))], 'mpbird', '%s <_ %s' % (KH, BS))
    K1 = '( %s + 1 )' % K0
    k1r = st([k0r], 'peano2red' if False else 'x', 'x') if False else ap_(w, A0, [k0r], 'peano2re', '%s e. RR' % K1)
    qk2 = st([qk, st([bsr, k1r, hp], 'ltdivmuld', '( %s < %s <-> %s < ( H x. %s ) )' % (Q, K1, BS, K1))], 'mpbid', '%s < ( H x. %s )' % (BS, K1))
    mr = st([mn], 'nn0red', 'M e. RR')
    c = _cl.Closure(w, A0, {})
    for E_, s_ in [('B', br), ('S', sr), ('U', ur), ('H', hr), (K0, k0r), ('M', mr)]:
        c.leaf(E_, 'RR', s_)
    MH = '( M x. H )'
    c.leaf(MH, 'RR', st([mr, hr], 'remulcld', '%s e. RR' % MH))
    c.leaf(KH, 'RR', st([k0r, hr], 'remulcld', '%s e. RR' % KH))
    HK1 = '( H x. %s )' % K1
    c.leaf(HK1, 'RR', st([hr, k1r], 'remulcld', '%s e. RR' % HK1))
    HM = '( H x. M )'
    hm = st([st([hr], 'recnd', 'H e. CC'), st([mr], 'recnd', 'M e. CC')], 'mulcomd', '%s = %s' % (HM, MH))
    c.leaf(HM, 'RR', st([hr, mr], 'remulcld', '%s e. RR' % HM))
    bm = lin.linarith(w, A0, [bu, um, hm], '%s < %s' % (BS, HM), closure=c)
    qm = st([bm, st([bsr, mr, hp], 'ltdivmuld', '( %s < M <-> %s < %s )' % (Q, BS, HM))], 'mpbird', '%s < M' % Q)
    c.leaf(Q, 'RR', qr)
    km = lin.linarith(w, A0, [kq, qm], '%s < M' % K0, closure=c)
    mz = st([mn], 'nn0zd', 'M e. ZZ')
    m0 = lin.linarith(w, A0, [km, st([k0], 'nn0ge0d', '0 <_ %s' % K0)], '0 < M', closure=c)
    mnn = w.s([st([mz, m0], 'jca', '( M e. ZZ /\\ 0 < M )'), w.s([], 'elnnz', '( M e. NN <-> ( M e. ZZ /\\ 0 < M ) )')], 'sylibr', '( %s -> M e. NN )' % A0)
    kin = w.s([st([k0, mnn, km], '3jca', '( %s e. NN0 /\\ M e. NN /\\ %s < M )' % (K0, K0)), w.s([], 'elfzo0', '( %s e. ( 0 ..^ M ) <-> ( %s e. NN0 /\\ M e. NN /\\ %s < M ) )' % (K0, K0, K0))], 'sylibr', '( %s -> %s e. ( 0 ..^ M ) )' % (A0, K0))
    cond = lin.linarith(w, A0, [kh], '( S + %s ) <_ B' % KH, closure=c)
    E1 = '( S + ( %s x. H ) )' % K1
    c.leaf('( %s x. H )' % K1, 'RR', st([k1r, hr], 'remulcld', '( %s x. H ) e. RR' % K1))
    hk = st([st([hr], 'recnd', 'H e. CC'), st([k1r], 'recnd', '%s e. CC' % K1)], 'mulcomd', '%s = ( %s x. H )' % (HK1, K1))
    be = lin.linarith(w, A0, [qk2, hk], 'B <_ %s' % E1, closure=c)
    e1r = st([sr, st([k1r, hr], 'remulcld', '( %s x. H ) e. RR' % K1)], 'readdcld', '%s e. RR' % E1)
    yb = st([yr, y1, br, e1r, be], 'cxplead', '( Y ^c B ) <_ ( Y ^c %s )' % E1)
    y0 = lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr})
    ybr = st([yr, y0, br], 'recxpcld', '( Y ^c B ) e. RR'); yer = st([yr, y0, e1r], 'recxpcld', '( Y ^c %s ) e. RR' % E1)
    vyb = st([ybr, yer, vr, v0, yb], 'lemul2ad', '( V x. ( Y ^c B ) ) <_ ( V x. ( Y ^c %s ) )' % E1)
    TERM = 'if ( ( S + %s ) <_ B , ( V x. ( Y ^c %s ) ) , 0 )' % (KH, E1)
    it = st([cond], 'iftrued', '%s = ( V x. ( Y ^c %s ) )' % (TERM, E1))
    # body facts
    C1 = '( %s /\\ k e. ( 0 ..^ M ) )' % A0
    kn = ap_(w, C1, [w.s([], 'simpr', '( %s -> k e. ( 0 ..^ M ) )' % C1)], 'elfzonn0', 'k e. NN0')
    kr = w.s([kn], 'nn0red', '( %s -> k e. RR )' % C1)
    L = lambda s_: _cl.lift(w, s_, C1)
    Ek = '( S + ( ( k + 1 ) x. H ) )'
    ekr = w.s([L(sr), w.s([ap_(w, C1, [kr], 'peano2re', '( k + 1 ) e. RR'), L(hr)], 'remulcld', '( %s -> ( ( k + 1 ) x. H ) e. RR )' % C1)], 'readdcld', '( %s -> %s e. RR )' % (C1, Ek))
    yek = w.s([L(yr), L(y0), ekr], 'recxpcld', '( %s -> ( Y ^c %s ) e. RR )' % (C1, Ek))
    ye0 = w.s([L(yr), L(y0), ekr], 'cxpge0d', '( %s -> 0 <_ ( Y ^c %s ) )' % (C1, Ek))
    vbr = w.s([L(vr), yek], 'remulcld', '( %s -> ( V x. ( Y ^c %s ) ) e. RR )' % (C1, Ek))
    vb0 = w.s([L(vr), yek, L(v0), ye0], 'mulge0d', '( %s -> 0 <_ ( V x. ( Y ^c %s ) ) )' % (C1, Ek))
    ir, i0 = ifnn(w, C1, '( S + ( k x. H ) ) <_ B', '( V x. ( Y ^c %s ) )' % Ek, vbr, vb0)
    H_ = 'k = %s' % K0
    sb_ = w.s([w.s([w.s([w.s([], 'oveq1', '( %s -> ( k x. H ) = ( %s x. H ) )' % (H_, K0))], 'oveq2d', '( %s -> ( S + ( k x. H ) ) = ( S + %s ) )' % (H_, KH))], 'breq1d', '( %s -> ( ( S + ( k x. H ) ) <_ B <-> ( S + %s ) <_ B ) )' % (H_, KH)),
               w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( %s -> ( k + 1 ) = %s )' % (H_, K1))], 'oveq1d', '( %s -> ( ( k + 1 ) x. H ) = ( %s x. H ) )' % (H_, K1))], 'oveq2d', '( %s -> %s = %s )' % (H_, Ek, E1))], 'oveq2d', '( %s -> ( Y ^c %s ) = ( Y ^c %s ) )' % (H_, Ek, E1))], 'oveq2d',
                   '( %s -> ( V x. ( Y ^c %s ) ) = ( V x. ( Y ^c %s ) ) )' % (H_, Ek, E1)),
               w.s([], 'eqidd', '( %s -> 0 = 0 )' % H_)], 'ifbieq12d', '( %s -> if ( ( S + ( k x. H ) ) <_ B , ( V x. ( Y ^c %s ) ) , 0 ) = %s )' % (H_, Ek, TERM))
    ge = st([st([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin'), ir, i0, sb_, kin], 'fsumge1', '%s <_ %s' % (TERM, GRIDS))
    fin = st([st([vyb, it], 'breqtrrd', '( V x. ( Y ^c B ) ) <_ %s' % TERM), ge], 'x', 'x') if False else None
    trm = st([st([vr, yer], 'remulcld', '( V x. ( Y ^c %s ) ) e. RR' % E1), it], 'x', 'x') if False else None
    termr = st([it, st([vr, yer], 'remulcld', '( V x. ( Y ^c %s ) ) e. RR' % E1)], 'eqeltrd', '%s e. RR' % TERM)
    sumr = st([st([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin'), ir], 'fsumrecl', '%s e. RR' % GRIDS)
    fin = st([st([vr, ybr], 'remulcld', '( V x. ( Y ^c B ) ) e. RR'), termr, sumr, st([vyb, it], 'breqtrrd', '( V x. ( Y ^c B ) ) <_ %s' % TERM), ge], 'letrd', '( V x. ( Y ^c B ) ) <_ %s' % GRIDS)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21gridr']))
    return run(w)

def gen_grid():
    w = W('t21grid', 'sigma-grid bound: zeros ` q ` with ` S <_ Re q < U ` , weights ` V >_ 0 ` , tails ` C ( x , k ) ` containing every zero with ` Re q >_ S + k H ` of mass ` <_ D ( k ) ` : ` sum sum V Y ^ Re q <_ sum_ ( k < M ) Y ^ ( S + ( k + 1 ) H ) D ( k ) ` (Lean ` grid_bound ` ; ~ t21gridr , ~ sumss2 , ~ rabss ).')
    for k in sorted(GRIDH):
        w.lines.append('h%d::t21grid.%d |- %s' % (k, k, GRIDH[k]))
    C0 = 'ph'; C1 = '( ph /\\ x e. I )'; C2 = '( %s /\\ q e. A )' % C1; FZ = '( 0 ..^ M )'
    C3 = '( %s /\\ k e. %s )' % (C2, FZ)
    s = lambda A_, h, r, f: w.s(h, r, '( %s -> %s )' % (A_, f))
    L = lambda st_, A_: _cl.lift(w, st_, A_)
    h5 = '5'
    yy = s(C0, [h5], 'simp1d', '( Y e. RR /\\ 1 <_ Y )'); hm = s(C0, [h5], 'simp2d', '( H e. RR+ /\\ M e. NN0 )'); su = s(C0, [h5], 'simp3d', '( ( S e. RR /\\ U e. RR ) /\\ U <_ ( S + ( M x. H ) ) )')
    yr = s(C0, [yy], 'simpld', 'Y e. RR'); y1 = s(C0, [yy], 'simprd', '1 <_ Y'); hp = s(C0, [hm], 'simpld', 'H e. RR+'); mn = s(C0, [hm], 'simprd', 'M e. NN0')
    sr = s(C0, [s(C0, [su], 'simpld', '( S e. RR /\\ U e. RR )')], 'simpld', 'S e. RR'); ur = s(C0, [s(C0, [su], 'simpld', '( S e. RR /\\ U e. RR )')], 'simprd', 'U e. RR')
    um = s(C0, [su], 'simprd', 'U <_ ( S + ( M x. H ) )')
    y0 = lin.linarith(w, C0, [y1], '0 <_ Y', leaves={'Y': yr})
    h3 = '3'
    qv = s(C2, [h3], 'simpld', '( q e. CC /\\ ( V e. RR /\\ 0 <_ V ) )'); rr = s(C2, [h3], 'simprd', '( S <_ ( Re ` q ) /\\ ( Re ` q ) < U )')
    qc = s(C2, [qv], 'simpld', 'q e. CC'); vv = s(C2, [qv], 'simprd', '( V e. RR /\\ 0 <_ V )')
    vr = s(C2, [vv], 'simpld', 'V e. RR'); v0 = s(C2, [vv], 'simprd', '0 <_ V')
    re = s(C2, [qc], 'recld', '( Re ` q ) e. RR')
    Ek = '( S + ( ( k + 1 ) x. H ) )'; Yk = '( Y ^c %s )' % Ek
    CND = '( S + ( k x. H ) ) <_ ( Re ` q )'
    IF = 'if ( %s , ( V x. %s ) , 0 )' % (CND, Yk)
    SK = 'sum_ k e. %s %s' % (FZ, IF)
    pt = ap_(w, C2, [L(yr, C2), L(y1, C2), L(hp, C2), L(mn, C2), L(sr, C2), re, L(ur, C2), s(C2, [rr], 'simpld', 'S <_ ( Re ` q )'), s(C2, [rr], 'simprd', '( Re ` q ) < U'), L(um, C2), vr, v0],
             't21gridr', '( V x. ( Y ^c ( Re ` q ) ) ) <_ %s' % SK)
    # body facts under C3
    kn = ap_(w, C3, [w.s([], 'simpr', '( %s -> k e. %s )' % (C3, FZ))], 'elfzonn0', 'k e. NN0')
    kr = w.s([kn], 'nn0red', '( %s -> k e. RR )' % C3)
    ekr = w.s([L(sr, C3), w.s([ap_(w, C3, [kr], 'peano2re', '( k + 1 ) e. RR'), L(s(C0, [hp], 'rpred', 'H e. RR'), C3)], 'remulcld', '( %s -> ( ( k + 1 ) x. H ) e. RR )' % C3)], 'readdcld', '( %s -> %s e. RR )' % (C3, Ek))
    ykr = w.s([L(yr, C3), L(y0, C3), ekr], 'recxpcld', '( %s -> %s e. RR )' % (C3, Yk))
    yk0 = w.s([L(yr, C3), L(y0, C3), ekr], 'cxpge0d', '( %s -> 0 <_ %s )' % (C3, Yk))
    vyr = w.s([L(vr, C3), ykr], 'remulcld', '( %s -> ( V x. %s ) e. RR )' % (C3, Yk))
    vy0 = w.s([L(vr, C3), ykr, L(v0, C3), yk0], 'mulge0d', '( %s -> 0 <_ ( V x. %s ) )' % (C3, Yk))
    ifr, if0 = ifnn(w, C3, CND, '( V x. %s )' % Yk, vyr, vy0)
    fz = s(C0, [w.s([], 'fzofi', '%s e. Fin' % FZ)], 'a1i', '%s e. Fin' % FZ)
    skr = s(C2, [L(fz, C2), ifr], 'fsumrecl', '%s e. RR' % SK)
    vyq = s(C2, [vr, s(C2, [L(yr, C2), L(y0, C2), re], 'recxpcld', '( Y ^c ( Re ` q ) ) e. RR')], 'remulcld', '( V x. ( Y ^c ( Re ` q ) ) ) e. RR')
    # sum over q (C1), then x (C0)
    a1 = s(C1, ['2', vyq, skr, pt], 'fsumle', 'sum_ q e. A ( V x. ( Y ^c ( Re ` q ) ) ) <_ sum_ q e. A %s' % SK)
    C4 = '( %s /\\ ( q e. A /\\ k e. %s ) )' % (C1, FZ)
    m43 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (C4, C1)), w.s([w.s([], 'simpr', '( %s -> ( q e. A /\\ k e. %s ) )' % (C4, FZ))], 'simpld', '( %s -> q e. A )' % C4)], 'jca', '( %s -> %s )' % (C4, C2)),
               w.s([w.s([], 'simpr', '( %s -> ( q e. A /\\ k e. %s ) )' % (C4, FZ))], 'simprd', '( %s -> k e. %s )' % (C4, FZ))], 'jca', '( %s -> %s )' % (C4, C3))
    ifc4 = w.s([m43, w.s([ifr], 'recnd', '( %s -> %s e. CC )' % (C3, IF))], 'syl', '( %s -> %s e. CC )' % (C4, IF))
    SQK = 'sum_ k e. %s sum_ q e. A %s' % (FZ, IF)
    a2 = s(C1, ['2', L(fz, C1), ifc4], 'fsumcom', 'sum_ q e. A %s = %s' % (SK, SQK))
    # ---- per k
    Ck = '( ph /\\ k e. %s )' % FZ; Ckx = '( %s /\\ x e. I )' % Ck
    mk = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckx, Ck))], 'simpld', '( %s -> ph )' % Ckx), w.s([], 'simpr', '( %s -> x e. I )' % Ckx)], 'jca', '( %s -> %s )' % (Ckx, C1)),
              w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckx, Ck))], 'simprd', '( %s -> k e. %s )' % (Ckx, FZ))], 'jca', '( %s -> ( %s /\\ k e. %s ) )' % (Ckx, C1, FZ))
    H4 = '( C e. Fin /\\ A. q e. C ( V e. RR /\\ 0 <_ V ) /\\ A. q e. A ( %s -> q e. C ) )' % CND
    h4 = w.s([mk, '4'], 'syl', '( %s -> %s )' % (Ckx, H4))
    cfin = s(Ckx, [h4], 'simp1d', 'C e. Fin')
    cv = s(Ckx, [h4], 'simp2d', 'A. q e. C ( V e. RR /\\ 0 <_ V )')
    ca = s(Ckx, [h4], 'simp3d', 'A. q e. A ( %s -> q e. C )' % CND)
    CNDj = '( S + ( k x. H ) ) <_ ( Re ` j )'
    R = '{ j e. A | %s }' % CNDj
    cb = w.s([w.s([w.s([w.s([], 'fveq2', '( q = j -> ( Re ` q ) = ( Re ` j ) )')], 'breq2d', '( q = j -> ( %s <-> %s ) )' % (CND, CNDj)),
                   w.s([], 'eleq1w', '( q = j -> ( q e. C <-> j e. C ) )')], 'imbi12d', '( q = j -> ( ( %s -> q e. C ) <-> ( %s -> j e. C ) ) )' % (CND, CNDj))], 'cbvralvw',
             '( A. q e. A ( %s -> q e. C ) <-> A. j e. A ( %s -> j e. C ) )' % (CND, CNDj))
    rs = s(Ckx, [s(Ckx, [ca, s(Ckx, [cb], 'a1i' if False else 'x', 'x') if False else w.s([cb], 'a1i', '( %s -> ( A. q e. A ( %s -> q e. C ) <-> A. j e. A ( %s -> j e. C ) ) )' % (Ckx, CND, CNDj))], 'mpbid', 'A. j e. A ( %s -> j e. C )' % CNDj),
                     w.s([], 'rabss', '( %s C_ C <-> A. j e. A ( %s -> j e. C ) )' % (R, CNDj)) and w.s([w.s([], 'rabss', '( %s C_ C <-> A. j e. A ( %s -> j e. C ) )' % (R, CNDj))], 'a1i', '( %s -> ( %s C_ C <-> A. j e. A ( %s -> j e. C ) ) )' % (Ckx, R, CNDj))], 'mpbird', '%s C_ C' % R)
    Ckxq = '( %s /\\ q e. A )' % Ckx
    mq = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckxq, Ckx)), mk], 'syl', '( %s -> ( %s /\\ k e. %s ) )' % (Ckxq, C1, FZ)), w.s([], 'simpr', '( %s -> q e. A )' % Ckxq)], 'x', 'x') if False else None
    c1k = w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckxq, Ckx)), w.s([mk], 'simpld', '( %s -> %s )' % (Ckx, C1))], 'syl', '( %s -> %s )' % (Ckxq, C1))
    kq = w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckxq, Ckx)), w.s([mk], 'simprd', '( %s -> k e. %s )' % (Ckx, FZ))], 'syl', '( %s -> k e. %s )' % (Ckxq, FZ))
    m3 = w.s([w.s([c1k, w.s([], 'simpr', '( %s -> q e. A )' % Ckxq)], 'jca', '( %s -> %s )' % (Ckxq, C2)), kq], 'jca', '( %s -> %s )' % (Ckxq, C3))
    elr = w.s([w.s([w.s([], 'fveq2', '( j = q -> ( Re ` j ) = ( Re ` q ) )')], 'breq2d', '( j = q -> ( %s <-> %s ) )' % (CNDj, CND))], 'elrab', '( q e. %s <-> ( q e. A /\\ %s ) )' % (R, CND))
    bi = w.s([w.s([w.s([], 'simpr', '( %s -> q e. A )' % Ckxq)], 'biantrurd', '( %s -> ( %s <-> ( q e. A /\\ %s ) ) )' % (Ckxq, CND, CND)), w.s([elr], 'a1i', '( %s -> ( q e. %s <-> ( q e. A /\\ %s ) ) )' % (Ckxq, R, CND))], 'bitr4d',
             '( %s -> ( %s <-> q e. %s ) )' % (Ckxq, CND, R))
    IFR = 'if ( q e. %s , ( V x. %s ) , 0 )' % (R, Yk)
    ib = w.s([bi], 'ifbid', '( %s -> %s = %s )' % (Ckxq, IF, IFR))
    e1 = s(Ckx, [ib], 'sumeq2dv', 'sum_ q e. A %s = sum_ q e. A %s' % (IF, IFR))
    Ckxr = '( %s /\\ q e. %s )' % (Ckx, R)
    qa = w.s([w.s([w.s([], 'ssrab2', '%s C_ A' % R)], 'a1i', '( %s -> %s C_ A )' % (Ckxr, R)), w.s([], 'simpr', '( %s -> q e. %s )' % (Ckxr, R))], 'sseldd', '( %s -> q e. A )' % Ckxr)
    c1r = w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckxr, Ckx)), w.s([mk], 'simpld', '( %s -> %s )' % (Ckx, C1))], 'syl', '( %s -> %s )' % (Ckxr, C1))
    kr_ = w.s([w.s([], 'simpl', '( %s -> %s )' % (Ckxr, Ckx)), w.s([mk], 'simprd', '( %s -> k e. %s )' % (Ckx, FZ))], 'syl', '( %s -> k e. %s )' % (Ckxr, FZ))
    m3r = w.s([w.s([c1r, qa], 'jca', '( %s -> %s )' % (Ckxr, C2)), kr_], 'jca', '( %s -> %s )' % (Ckxr, C3))
    vyc = w.s([m3r, w.s([vyr], 'recnd', '( %s -> ( V x. %s ) e. CC )' % (C3, Yk))], 'syl', '( %s -> ( V x. %s ) e. CC )' % (Ckxr, Yk))
    ral = s(Ckx, [vyc], 'ralrimiva', 'A. q e. %s ( V x. %s ) e. CC' % (R, Yk))
    afin = w.s([w.s([mk], 'simpld', '( %s -> %s )' % (Ckx, C1)), '2'], 'syl', '( %s -> A e. Fin )' % Ckx)
    orf = s(Ckx, [afin], 'olcd', '( A C_ ( ZZ>= ` 1 ) \\/ A e. Fin )')
    ss2 = ap_(w, Ckx, [s(Ckx, [w.s([], 'ssrab2', '%s C_ A' % R)], 'a1i', '%s C_ A' % R), ral, orf], 'sumss2', 'sum_ q e. %s ( V x. %s ) = sum_ q e. A %s' % (R, Yk, IFR))
    # V on C
    Ckxc = '( %s /\\ q e. C )' % Ckx
    vvc = w.s([w.s([L(cv, Ckxc), w.s([], 'simpr', '( %s -> q e. C )' % Ckxc), w.s([], 'rsp', '( A. q e. C ( V e. RR /\\ 0 <_ V ) -> ( q e. C -> ( V e. RR /\\ 0 <_ V ) ) )')], 'sylc', '( %s -> ( V e. RR /\\ 0 <_ V ) )' % Ckxc)], 'x', 'x') if False else w.s([L(cv, Ckxc), w.s([], 'simpr', '( %s -> q e. C )' % Ckxc), w.s([], 'rsp', '( A. q e. C ( V e. RR /\\ 0 <_ V ) -> ( q e. C -> ( V e. RR /\\ 0 <_ V ) ) )')], 'sylc', '( %s -> ( V e. RR /\\ 0 <_ V ) )' % Ckxc)
    vrc = w.s([vvc], 'simpld', '( %s -> V e. RR )' % Ckxc); v0c = w.s([vvc], 'simprd', '( %s -> 0 <_ V )' % Ckxc)
    # Yk under Ck (no q)
    knk = ap_(w, Ck, [w.s([], 'simpr', '( %s -> k e. %s )' % (Ck, FZ))], 'elfzonn0', 'k e. NN0')
    ekk = w.s([L(sr, Ck), w.s([ap_(w, Ck, [w.s([knk], 'nn0red', '( %s -> k e. RR )' % Ck)], 'peano2re', '( k + 1 ) e. RR'), L(s(C0, [hp], 'rpred', 'H e. RR'), Ck)], 'remulcld', '( %s -> ( ( k + 1 ) x. H ) e. RR )' % Ck)], 'readdcld', '( %s -> %s e. RR )' % (Ck, Ek))
    ykk = w.s([L(yr, Ck), L(y0, Ck), ekk], 'recxpcld', '( %s -> %s e. RR )' % (Ck, Yk))
    yk0k = w.s([L(yr, Ck), L(y0, Ck), ekk], 'cxpge0d', '( %s -> 0 <_ %s )' % (Ck, Yk))
    vyc_r = w.s([vrc, L(ykk, Ckxc)], 'remulcld', '( %s -> ( V x. %s ) e. RR )' % (Ckxc, Yk))
    vyc_0 = w.s([vrc, L(ykk, Ckxc), v0c, L(yk0k, Ckxc)], 'mulge0d', '( %s -> 0 <_ ( V x. %s ) )' % (Ckxc, Yk))
    le1 = s(Ckx, [cfin, vyc_r, vyc_0, rs], 'fsumless', 'sum_ q e. %s ( V x. %s ) <_ sum_ q e. C ( V x. %s )' % (R, Yk, Yk))
    mc1 = s(Ckx, [cfin, L(s(Ck, [ykk], 'recnd', '%s e. CC' % Yk), Ckx), w.s([vrc], 'recnd', '( %s -> V e. CC )' % Ckxc)], 'fsummulc1', '( sum_ q e. C V x. %s ) = sum_ q e. C ( V x. %s )' % (Yk, Yk))
    SA = 'sum_ q e. A %s' % IF
    per_x = s(Ckx, [s(Ckx, [e1, ss2], 'eqtr4d', '%s = sum_ q e. %s ( V x. %s )' % (SA, R, Yk)), s(Ckx, [le1, mc1], 'breqtrrd', 'sum_ q e. %s ( V x. %s ) <_ ( sum_ q e. C V x. %s )' % (R, Yk, Yk))], 'eqbrtrd',
              '%s <_ ( sum_ q e. C V x. %s )' % (SA, Yk))
    sar = w.s([afin, w.s([w.s([w.s([w.s([], 'simpl', '( ( %s /\\ q e. A ) -> %s )' % (Ckx, Ckx)), w.s([], 'simpr', '( ( %s /\\ q e. A ) -> q e. A )' % Ckx)], 'jca', '( ( %s /\\ q e. A ) -> ( %s /\\ q e. A ) )' % (Ckx, Ckx)), m3], 'syl', '( %s -> %s )' % (Ckxq, C3)), ifr], 'syl', '( %s -> %s e. RR )' % (Ckxq, IF))], 'fsumrecl', '( %s -> %s e. RR )' % (Ckx, SA))
    scr = s(Ckx, [s(Ckx, [cfin, vrc], 'fsumrecl', 'sum_ q e. C V e. RR'), L(ykk, Ckx)], 'remulcld', '( sum_ q e. C V x. %s ) e. RR' % Yk)
    ifin = s(Ck, [w.s([], 'simpl', '( %s -> ph )' % Ck), '1'], 'x', 'x') if False else w.s([w.s([], 'simpl', '( %s -> ph )' % Ck), '1'], 'syl', '( %s -> I e. Fin )' % Ck)
    b1 = s(Ck, [ifin, sar, scr, per_x], 'fsumle', 'sum_ x e. I %s <_ sum_ x e. I ( sum_ q e. C V x. %s )' % (SA, Yk))
    SXC = 'sum_ x e. I sum_ q e. C V'
    b2 = s(Ck, [ifin, s(Ck, [ykk], 'recnd', '%s e. CC' % Yk), w.s([s(Ckx, [cfin, vrc], 'fsumrecl', 'sum_ q e. C V e. RR')], 'recnd', '( %s -> sum_ q e. C V e. CC )' % Ckx)], 'fsummulc1',
           '( %s x. %s ) = sum_ x e. I ( sum_ q e. C V x. %s )' % (SXC, Yk, Yk))
    h6 = '6'
    dr = s(Ck, [h6], 'simpld', 'D e. RR'); dle = s(Ck, [h6], 'simprd', '%s <_ D' % SXC)
    sxcr = s(Ck, [ifin, s(Ckx, [cfin, vrc], 'fsumrecl', 'sum_ q e. C V e. RR')], 'fsumrecl', '%s e. RR' % SXC)
    b3 = s(Ck, [sxcr, dr, ykk, yk0k, dle], 'lemul1ad', '( %s x. %s ) <_ ( D x. %s )' % (SXC, Yk, Yk))
    b4 = s(Ck, [s(Ck, [dr], 'recnd', 'D e. CC'), s(Ck, [ykk], 'recnd', '%s e. CC' % Yk)], 'mulcomd', '( D x. %s ) = ( %s x. D )' % (Yk, Yk))
    SXA = 'sum_ x e. I %s' % SA
    perk = s(Ck, [s(Ck, [b1, s(Ck, [b2], 'eqcomd', 'sum_ x e. I ( sum_ q e. C V x. %s ) = ( %s x. %s )' % (Yk, SXC, Yk))], 'breqtrd', '%s <_ ( %s x. %s )' % (SXA, SXC, Yk)), s(Ck, [b3, b4], 'breqtrd', '( %s x. %s ) <_ ( %s x. D )' % (SXC, Yk, Yk))], 'x', 'x') if False else None
    xar = s(Ck, [ifin, sar], 'fsumrecl', '%s e. RR' % SXA)
    t1 = s(Ck, [b1, s(Ck, [b2], 'eqcomd', 'sum_ x e. I ( sum_ q e. C V x. %s ) = ( %s x. %s )' % (Yk, SXC, Yk))], 'breqtrd', '%s <_ ( %s x. %s )' % (SXA, SXC, Yk))
    t2 = s(Ck, [b3, b4], 'breqtrd', '( %s x. %s ) <_ ( %s x. D )' % (SXC, Yk, Yk))
    perk = s(Ck, [xar, s(Ck, [sxcr, ykk], 'remulcld', '( %s x. %s ) e. RR' % (SXC, Yk)), s(Ck, [ykk, dr], 'remulcld', '( %s x. D ) e. RR' % Yk), t1, t2], 'letrd', '%s <_ ( %s x. D )' % (SXA, Yk))
    # ---- assemble at ph
    SXQ = 'sum_ x e. I sum_ q e. A ( V x. ( Y ^c ( Re ` q ) ) )'
    SXQK = 'sum_ x e. I sum_ q e. A %s' % SK
    SXKQ = 'sum_ x e. I %s' % SQK
    SKXQ = 'sum_ k e. %s %s' % (FZ, SXA)
    c1 = s(C0, ['1', s(C1, ['2', vyq], 'fsumrecl', 'sum_ q e. A ( V x. ( Y ^c ( Re ` q ) ) ) e. RR'), s(C1, ['2', skr], 'fsumrecl', 'sum_ q e. A %s e. RR' % SK), a1], 'fsumle', '%s <_ %s' % (SXQ, SXQK))
    c2 = s(C0, [a2], 'sumeq2dv', '%s = %s' % (SXQK, SXKQ))
    C6 = '( ph /\\ ( x e. I /\\ k e. %s ) )' % FZ
    m6 = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % C6), w.s([w.s([], 'simpr', '( %s -> ( x e. I /\\ k e. %s ) )' % (C6, FZ))], 'simprd', '( %s -> k e. %s )' % (C6, FZ))], 'jca', '( %s -> %s )' % (C6, Ck)),
              w.s([w.s([], 'simpr', '( %s -> ( x e. I /\\ k e. %s ) )' % (C6, FZ))], 'simpld', '( %s -> x e. I )' % C6)], 'jca', '( %s -> %s )' % (C6, Ckx))
    sac = w.s([m6, w.s([sar], 'recnd', '( %s -> %s e. CC )' % (Ckx, SA))], 'syl', '( %s -> %s e. CC )' % (C6, SA))
    c3 = s(C0, ['1', fz, sac], 'fsumcom', '%s = %s' % (SXKQ, SKXQ))
    FINR = 'sum_ k e. %s ( %s x. D )' % (FZ, Yk)
    c4 = s(C0, [fz, xar, s(Ck, [ykk, dr], 'remulcld', '( %s x. D ) e. RR' % Yk), perk], 'fsumle', '%s <_ %s' % (SKXQ, FINR))
    fin = s(C0, [s(C0, [c1, s(C0, [c2, c3], 'eqtrd', '%s = %s' % (SXQK, SKXQ))], 'breqtrd', '%s <_ %s' % (SXQ, SKXQ)), c4], 'x', 'x') if False else None
    sxq_r = s(C0, ['1', s(C1, ['2', vyq], 'fsumrecl', 'sum_ q e. A ( V x. ( Y ^c ( Re ` q ) ) ) e. RR')], 'fsumrecl', '%s e. RR' % SXQ)
    skxq_r = s(C0, [fz, xar], 'fsumrecl', '%s e. RR' % SKXQ)
    finr_ = s(C0, [fz, s(Ck, [ykk, dr], 'remulcld', '( %s x. D ) e. RR' % Yk)], 'fsumrecl', '%s e. RR' % FINR)
    fin = s(C0, [sxq_r, skxq_r, finr_, s(C0, [c1, s(C0, [c2, c3], 'eqtrd', '%s = %s' % (SXQK, SKXQ))], 'breqtrd', '%s <_ %s' % (SXQ, SKXQ)), c4], 'letrd', '%s <_ %s' % (SXQ, FINR))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21grid']))
    return run(w)

def gen_gterm():
    w = W('t21gterm', 'One term of the geometric grid sum: at ` sigma = S + K / log X <_ T <_ 1 ` with ` J + K <_ ( T - S ) log X ` , ` Y ^ ( sigma + 1 / log X ) D ^ ( ( 9 / 2 ) ( 1 - sigma ) ) <_ e Y X ^ ( - ( 9 / 200 ) ( 1 - T ) ) exp ( - 9 / 200 ) ^ J ` , using ` Y ^ ( 1 / log X ) <_ e ` and ` D ^ ( 9 / 2 ) <_ X ^ ( - 9 / 200 ) Y ` (Lean ` grid_geom ` , ` hterm ` ).')
    A0 = ante_of(S['t21gterm'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    L = LX; h = LH; sg = SGK; E = EXPT; r = RR9
    xr, xe, yr, y1, yx, dr, d1, dy, sr, tr, t1, jn, kr, sT, jk = [u[k] for k in ['X e. RR', '( exp ` 1 ) <_ X', 'Y e. RR', '1 <_ Y', 'Y <_ X', 'D e. RR', '1 <_ D',
        '( D ^c %s ) <_ ( ( X ^c -u %s ) x. Y )' % (F92, F9200), 'S e. RR', 'T e. RR', 'T <_ 1', 'J e. NN0', 'K e. RR', '%s <_ T' % sg, '( J + K ) <_ ( ( T - S ) x. %s )' % L]]
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    e1p = st([one], 'rpefcld', '( exp ` 1 ) e. RR+')
    e1r = st([e1p], 'rpred', '( exp ` 1 ) e. RR')
    xp = st([xr, st([st([e1p], 'rpgt0d', '0 < ( exp ` 1 )'), xe], 'x', 'x') if False else lin.linarith(w, A0, [st([e1p], 'rpgt0d', '0 < ( exp ` 1 )'), xe], '0 < X', leaves={'X': xr, '( exp ` 1 )': e1r})], 'elrpd', 'X e. RR+')
    lg = st([st([e1p, xp], 'logled', '( ( exp ` 1 ) <_ X <-> ( log ` ( exp ` 1 ) ) <_ %s )' % L), xe], 'x', 'x') if False else None
    lge = st([xe, st([e1p, xp], 'logled', '( ( exp ` 1 ) <_ X <-> ( log ` ( exp ` 1 ) ) <_ %s )' % L)], 'mpbid', '( log ` ( exp ` 1 ) ) <_ %s' % L)
    l1 = st([st([ap_(w, A0, [one], 'relogef', '( log ` ( exp ` 1 ) ) = 1')], 'eqcomd', '1 = ( log ` ( exp ` 1 ) )'), lge], 'eqbrtrd', '1 <_ %s' % L)
    lr = st([xp], 'relogcld', '%s e. RR' % L)
    lp = st([lr, lin.linarith(w, A0, [l1], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    hp = st([lp], 'rpreccld', '%s e. RR+' % h); hr = st([hp], 'rpred', '%s e. RR' % h)
    KH = '( K x. %s )' % h
    khr = st([kr, hr], 'remulcld', '%s e. RR' % KH)
    sgr = st([sr, khr], 'readdcld', '%s e. RR' % sg)
    c = _cl.Closure(w, A0, {})
    for E_, s_ in [('S', sr), ('T', tr), ('K', kr), (KH, khr), (h, hr), (L, lr), ('Y', yr), ('X', xr), ('D', dr)]:
        c.leaf(E_, 'RR', s_)
    oms = '( 1 - %s )' % sg
    omr = st([one, sgr], 'resubcld', '%s e. RR' % oms)
    om0 = lin.linarith(w, A0, [sT, t1], '0 <_ %s' % oms, closure=c)
    yp = st([yr, lin.linarith(w, A0, [y1], '0 < Y', closure=c)], 'elrpd', 'Y e. RR+')
    y0 = st([yp], 'rpge0d', '0 <_ Y')
    yc = st([yp], 'rpcnd', 'Y e. CC'); yn = st([yp], 'rpne0d', 'Y =/= 0')
    # exponent S + ( K + 1 ) h = sigma + h
    ad = st([st([kr], 'recnd', 'K e. CC'), st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), st([hr], 'recnd', '%s e. CC' % h)], 'adddird', '( ( K + 1 ) x. %s ) = ( %s + ( 1 x. %s ) )' % (h, KH, h))
    ad2 = st([ad, st([st([st([hr], 'recnd', '%s e. CC' % h)], 'mullidd', '( 1 x. %s ) = %s' % (h, h))], 'oveq2d', '( %s + ( 1 x. %s ) ) = ( %s + %s )' % (KH, h, KH, h))], 'eqtrd', '( ( K + 1 ) x. %s ) = ( %s + %s )' % (h, KH, h))
    K1H = '( ( K + 1 ) x. %s )' % h
    c.leaf(K1H, 'RR', st([ap_(w, A0, [kr], 'peano2re', '( K + 1 ) e. RR'), hr], 'remulcld', '%s e. RR' % K1H))
    ex1 = lin.lineq(w, A0, '( S + %s )' % K1H, '( %s + %s )' % (sg, h), hyps=[ad2], closure=c)
    Ys, Yh = '( Y ^c %s )' % sg, '( Y ^c %s )' % h
    y5 = st([st([ex1], 'oveq2d', '( Y ^c ( S + %s ) ) = ( Y ^c ( %s + %s ) )' % (K1H, sg, h)), st([yc, yn, st([sgr], 'recnd', '%s e. CC' % sg), st([hr], 'recnd', '%s e. CC' % h)], 'cxpaddd', '( Y ^c ( %s + %s ) ) = ( %s x. %s )' % (sg, h, Ys, Yh))], 'eqtrd',
            '( Y ^c ( S + %s ) ) = ( %s x. %s )' % (K1H, Ys, Yh))
    # Y ^ h <_ e
    yh = st([yr, y0, xr, hr, st([hp], 'rpge0d', '0 <_ %s' % h), yx], 'cxple2ad', '%s <_ ( X ^c %s )' % (Yh, h))
    xh = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([hr], 'recnd', '%s e. CC' % h)], 'cxpefd', '( X ^c %s ) = ( exp ` ( %s x. %s ) )' % (h, h, L))
    hl = st([st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L)], 'recid2d', '( %s x. %s ) = 1' % (h, L))
    xh2 = st([xh, st([hl], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` 1 )' % (h, L))], 'eqtrd', '( X ^c %s ) = ( exp ` 1 )' % h)
    yhe = st([yh, xh2], 'breqtrd', '%s <_ ( exp ` 1 )' % Yh)
    # D power
    Dp = '( D ^c ( %s x. %s ) )' % (F92, oms)
    dp_ = st([dr, lin.linarith(w, A0, [d1], '0 < D', closure=c)], 'elrpd', 'D e. RR+')
    f92 = st([num.real(w, F92)], 'a1i', '%s e. RR' % F92)
    D92 = '( D ^c %s )' % F92
    dm = st([dp_, f92, st([omr], 'recnd', '%s e. CC' % oms)], 'cxpmuld', '%s = ( %s ^c %s )' % (Dp, D92, oms))
    XN = '( X ^c -u %s )' % F9200
    xnr = st([xp, st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200)], 'rpcxpcld', '%s e. RR+' % XN)
    XY = '( %s x. Y )' % XN
    xyr = st([st([xnr], 'rpred', '%s e. RR' % XN), yr], 'remulcld', '%s e. RR' % XY)
    d92r = st([dp_, f92], 'rpcxpcld', '%s e. RR+' % D92)
    dle = st([st([d92r], 'rpred', '%s e. RR' % D92), st([d92r], 'rpge0d', '0 <_ %s' % D92), xyr, omr, om0, dy], 'cxple2ad', '( %s ^c %s ) <_ ( %s ^c %s )' % (D92, oms, XY, oms))
    mc = st([st([xnr], 'rpred', '%s e. RR' % XN), st([xnr], 'rpge0d', '0 <_ %s' % XN), yr, y0, st([omr], 'recnd', '%s e. CC' % oms)], 'mulcxpd', '( %s ^c %s ) = ( ( %s ^c %s ) x. ( Y ^c %s ) )' % (XY, oms, XN, oms, oms))
    X1 = '( X ^c ( -u %s x. %s ) )' % (F9200, oms)
    xm = st([xp, st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200), st([omr], 'recnd', '%s e. CC' % oms)], 'cxpmuld', '%s = ( %s ^c %s )' % (X1, XN, oms))
    Ym = '( Y ^c %s )' % oms
    dle2 = st([st([dm, dle], 'eqbrtrd', '%s <_ ( %s ^c %s )' % (Dp, XY, oms)), st([mc, st([xm], 'oveq1d', '( %s x. %s ) = ( ( %s ^c %s ) x. %s )' % (X1, Ym, XN, oms, Ym))], 'eqtr4d', '( %s ^c %s ) = ( %s x. %s )' % (XY, oms, X1, Ym))], 'breqtrd',
              '%s <_ ( %s x. %s )' % (Dp, X1, Ym))
    # Y ^ sigma x. Y ^ ( 1 - sigma ) = Y
    yy = st([yc, yn, st([sgr], 'recnd', '%s e. CC' % sg), st([omr], 'recnd', '%s e. CC' % oms)], 'cxpaddd', '( Y ^c ( %s + %s ) ) = ( %s x. %s )' % (sg, oms, Ys, Ym))
    p3 = st([st([sgr], 'recnd', '%s e. CC' % sg), st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'pncan3d', '( %s + %s ) = 1' % (sg, oms))
    yy2 = st([st([st([p3], 'oveq2d', '( Y ^c ( %s + %s ) ) = ( Y ^c 1 )' % (sg, oms)), st([yc], 'cxp1d', '( Y ^c 1 ) = Y')], 'eqtrd', '( Y ^c ( %s + %s ) ) = Y' % (sg, oms)), yy], 'eqtr3d', '( %s x. %s ) = Y' % (Ys, Ym))
    # X1 = E x. X2
    TS = '( T - %s )' % sg
    X2 = '( X ^c ( -u %s x. %s ) )' % (F9200, TS)
    e9r = st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200)
    tsr = st([tr, sgr], 'resubcld', '%s e. RR' % TS)
    a_ = '( -u %s x. ( 1 - T ) )' % F9200; b_ = '( -u %s x. %s )' % (F9200, TS)
    c.leaf(sg, 'RR', sgr)
    exq = lin.lineq(w, A0, '( -u %s x. %s )' % (F9200, oms), '( %s + %s )' % (a_, b_), closure=c)
    xs = st([st([exq], 'oveq2d', '%s = ( X ^c ( %s + %s ) )' % (X1, a_, b_)), st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([st([e9r, st([one, tr], 'resubcld', '( 1 - T ) e. RR')], 'remulcld', '%s e. RR' % a_)], 'recnd', '%s e. CC' % a_),
                                      st([st([e9r, tsr], 'remulcld', '%s e. RR' % b_)], 'recnd', '%s e. CC' % b_)], 'cxpaddd', '( X ^c ( %s + %s ) ) = ( %s x. %s )' % (a_, b_, E, X2))], 'eqtrd', '%s = ( %s x. %s )' % (X1, E, X2))
    # X2 <_ r ^ J
    x2e = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([st([e9r, tsr], 'remulcld', '%s e. RR' % b_)], 'recnd', '%s e. CC' % b_)], 'cxpefd', '%s = ( exp ` ( %s x. %s ) )' % (X2, b_, L))
    P2 = '( %s x. %s )' % (TS, L); P1 = '( %s x. %s )' % (b_, L); TSL = '( ( T - S ) x. %s )' % L
    c2 = _cl.Closure(w, A0, {})
    for E_, s_ in [('S', sr), ('T', tr), (KH, khr)]:
        c2.leaf(E_, 'RR', s_)
    tsq = lin.lineq(w, A0, TS, '( ( T - S ) - %s )' % KH, closure=c2)
    sdd = st([st([st([tr, sr], 'resubcld', '( T - S ) e. RR')], 'recnd', '( T - S ) e. CC'), st([khr], 'recnd', '%s e. CC' % KH), st([lr], 'recnd', '%s e. CC' % L)], 'subdird', '( ( ( T - S ) - %s ) x. %s ) = ( %s - ( %s x. %s ) )' % (KH, L, TSL, KH, L))
    kl = st([st([st([kr], 'recnd', 'K e. CC'), st([hr], 'recnd', '%s e. CC' % h), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd', '( %s x. %s ) = ( K x. ( %s x. %s ) )' % (KH, L, h, L)),
             st([st([hl], 'oveq2d', '( K x. ( %s x. %s ) ) = ( K x. 1 )' % (h, L)), st([st([kr], 'recnd', 'K e. CC')], 'mulridd', '( K x. 1 ) = K')], 'eqtrd', '( K x. ( %s x. %s ) ) = K' % (h, L))], 'eqtrd', '( %s x. %s ) = K' % (KH, L))
    p2e = st([st([st([tsq], 'oveq1d', '%s = ( ( ( T - S ) - %s ) x. %s )' % (P2, KH, L)), sdd], 'eqtrd', '%s = ( %s - ( %s x. %s ) )' % (P2, TSL, KH, L)), st([kl], 'oveq2d', '( %s - ( %s x. %s ) ) = ( %s - K )' % (TSL, KH, L, TSL))], 'eqtrd', '%s = ( %s - K )' % (P2, TSL))
    p1e = st([st([e9r], 'recnd', '-u %s e. CC' % F9200), st([tsr], 'recnd', '%s e. CC' % TS), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd', '%s = ( -u %s x. %s )' % (P1, F9200, P2))
    for E_, s_ in [(P2, st([tsr, lr], 'remulcld', '%s e. RR' % P2)), (P1, st([st([e9r, tsr], 'remulcld', '%s e. RR' % b_), lr], 'remulcld', '%s e. RR' % P1)), (TSL, st([st([tr, sr], 'resubcld', '( T - S ) e. RR'), lr], 'remulcld', '%s e. RR' % TSL)),
                   ('J', st([jn], 'nn0red', 'J e. RR'))]:
        c.leaf(E_, 'RR', s_)
    JE = '( J x. -u %s )' % F9200
    c.leaf(JE, 'RR', st([st([jn], 'nn0red', 'J e. RR'), e9r], 'remulcld', '%s e. RR' % JE))
    jc = st([st([st([jn], 'nn0red', 'J e. RR')], 'recnd', 'J e. CC'), st([e9r], 'recnd', '-u %s e. CC' % F9200)], 'mulcomd', '%s = ( -u %s x. J )' % (JE, F9200))
    pl = lin.linarith(w, A0, [p1e, p2e, jk, jc], '%s <_ %s' % (P1, JE), closure=c)
    ef = ap_(w, A0, [c.mem(P1, 'RR'), c.mem(JE, 'RR')], 'efle', '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (P1, JE, P1, JE))
    ef2 = st([pl, ef], 'mpbid', '( exp ` %s ) <_ ( exp ` %s )' % (P1, JE))
    ex = ap_(w, A0, [st([e9r], 'recnd', '-u %s e. CC' % F9200), st([jn], 'nn0zd', 'J e. ZZ')], 'efexp', '( exp ` %s ) = ( %s ^ J )' % (JE, r))
    x2r = st([st([x2e, ef2], 'eqbrtrd', '%s <_ ( exp ` %s )' % (X2, JE)), ex], 'breqtrd', '%s <_ ( %s ^ J )' % (X2, r))
    # assembly
    nn_ = lambda E_: st([yr, y0, c.mem('0', 'RR') if False else yr], 'x', 'x') if False else None
    ysr = st([yr, y0, sgr], 'recxpcld', '%s e. RR' % Ys); ys0 = st([yr, y0, sgr], 'cxpge0d', '0 <_ %s' % Ys)
    yhr = st([yr, y0, hr], 'recxpcld', '%s e. RR' % Yh); yh0 = st([yr, y0, hr], 'cxpge0d', '0 <_ %s' % Yh)
    dpr = st([dr, st([dp_], 'rpge0d', '0 <_ D'), st([f92, omr], 'remulcld', '( %s x. %s ) e. RR' % (F92, oms))], 'recxpcld', '%s e. RR' % Dp)
    dp0 = st([dr, st([dp_], 'rpge0d', '0 <_ D'), st([f92, omr], 'remulcld', '( %s x. %s ) e. RR' % (F92, oms))], 'cxpge0d', '0 <_ %s' % Dp)
    ymr = st([yr, y0, omr], 'recxpcld', '%s e. RR' % Ym); ym0 = st([yr, y0, omr], 'cxpge0d', '0 <_ %s' % Ym)
    x1p = st([xp, st([e9r, omr], 'remulcld', '( -u %s x. %s ) e. RR' % (F9200, oms))], 'rpcxpcld', '%s e. RR+' % X1)
    x1r = st([x1p], 'rpred', '%s e. RR' % X1); x10 = st([x1p], 'rpge0d', '0 <_ %s' % X1)
    ep = st([xp, st([e9r, st([one, tr], 'resubcld', '( 1 - T ) e. RR')], 'remulcld', '%s e. RR' % a_)], 'rpcxpcld', '%s e. RR+' % E)
    er_ = st([ep], 'rpred', '%s e. RR' % E); e0_ = st([ep], 'rpge0d', '0 <_ %s' % E)
    x2p = st([xp, st([e9r, tsr], 'remulcld', '%s e. RR' % b_)], 'rpcxpcld', '%s e. RR+' % X2)
    x2r_ = st([x2p], 'rpred', '%s e. RR' % X2)
    rjr = st([st([st([e9r], 'reefcld', '%s e. RR' % r)], 'x', 'x') if False else st([e9r], 'reefcld', '%s e. RR' % r), jn], 'reexpcld', '( %s ^ J ) e. RR' % r)
    A1 = st([yhr, e1r, ysr, ys0, yhe], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( exp ` 1 ) )' % (Ys, Yh, Ys))
    A2 = st([st([ysr, yhr], 'remulcld', '( %s x. %s ) e. RR' % (Ys, Yh)), st([ysr, e1r], 'remulcld', '( %s x. ( exp ` 1 ) ) e. RR' % Ys), dpr, st([x1r, ymr], 'remulcld', '( %s x. %s ) e. RR' % (X1, Ym)),
             st([ysr, yhr, ys0, yh0], 'mulge0d', '0 <_ ( %s x. %s )' % (Ys, Yh)), dp0, A1, dle2], 'lemul12ad', '( ( %s x. %s ) x. %s ) <_ ( ( %s x. ( exp ` 1 ) ) x. ( %s x. %s ) )' % (Ys, Yh, Dp, Ys, X1, Ym))
    cc_ = lambda s_, E_: st([s_], 'recnd', '%s e. CC' % E_)
    e1 = '( exp ` 1 )'
    ab = '( %s x. %s )' % (Ys, e1)
    B1 = st([st([cc_(x1r, X1), cc_(ymr, Ym)], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (X1, Ym, Ym, X1))], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (ab, X1, Ym, ab, Ym, X1))
    B2 = st([cc_(ysr, Ys), cc_(e1r, e1), cc_(ymr, Ym), cc_(x1r, X1)], 'mul4d', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (ab, Ym, X1, Ys, Ym, e1, X1))
    B3 = st([yy2], 'oveq1d', '( ( %s x. %s ) x. ( %s x. %s ) ) = ( Y x. ( %s x. %s ) )' % (Ys, Ym, e1, X1, e1, X1))
    B4 = st([yc, cc_(e1r, e1), cc_(x1r, X1)], 'mulassd', '( ( Y x. %s ) x. %s ) = ( Y x. ( %s x. %s ) )' % (e1, X1, e1, X1))
    B5 = st([st([yc, cc_(e1r, e1)], 'mulcomd', '( Y x. %s ) = ( %s x. Y )' % (e1, e1))], 'oveq1d', '( ( Y x. %s ) x. %s ) = ( ( %s x. Y ) x. %s )' % (e1, X1, e1, X1))
    eY = '( %s x. Y )' % e1
    Bq = st([st([st([B1, B2], 'eqtrd', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (ab, X1, Ym, Ys, Ym, e1, X1)), B3], 'eqtrd', '( %s x. ( %s x. %s ) ) = ( Y x. ( %s x. %s ) )' % (ab, X1, Ym, e1, X1)),
             st([B4, B5], 'eqtr3d', '( Y x. ( %s x. %s ) ) = ( %s x. %s )' % (e1, X1, eY, X1))], 'eqtrd', '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (ab, X1, Ym, eY, X1))
    eyr = st([e1r, yr], 'remulcld', '%s e. RR' % eY)
    ey0 = st([e1r, yr, st([e1p], 'rpge0d', '0 <_ %s' % e1), y0], 'mulge0d', '0 <_ %s' % eY)
    C1_ = st([x2r_, rjr, er_, e0_, x2r], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s ^ J ) )' % (E, X2, E, r))
    C2_ = st([st([er_, x2r_], 'remulcld', '( %s x. %s ) e. RR' % (E, X2)), st([er_, rjr], 'remulcld', '( %s x. ( %s ^ J ) ) e. RR' % (E, r)), eyr, ey0, C1_], 'lemul2ad',
             '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. ( %s ^ J ) ) )' % (eY, E, X2, eY, E, r))
    C3_ = st([st([xs], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (eY, X1, eY, E, X2)), C2_], 'eqbrtrd', '( %s x. %s ) <_ ( %s x. ( %s x. ( %s ^ J ) ) )' % (eY, X1, eY, E, r))
    lhs0 = '( ( Y ^c ( S + %s ) ) x. %s )' % (K1H, Dp)
    D1 = st([y5], 'oveq1d', '%s = ( ( %s x. %s ) x. %s )' % (lhs0, Ys, Yh, Dp))
    D2 = st([st([D1, A2], 'eqbrtrd', '%s <_ ( %s x. ( %s x. %s ) )' % (lhs0, ab, X1, Ym)), Bq], 'breqtrd', '%s <_ ( %s x. %s )' % (lhs0, eY, X1))
    lhsr = st([st([ysr, yhr], 'remulcld', '( %s x. %s ) e. RR' % (Ys, Yh)), dpr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (Ys, Yh, Dp))
    lr0 = st([D1, lhsr], 'eqeltrd', '%s e. RR' % lhs0)
    fin = st([lr0, st([eyr, x1r], 'remulcld', '( %s x. %s ) e. RR' % (eY, X1)), st([eyr, st([er_, rjr], 'remulcld', '( %s x. ( %s ^ J ) ) e. RR' % (E, r))], 'remulcld', '( %s x. ( %s x. ( %s ^ J ) ) ) e. RR' % (eY, E, r)), D2, C3_], 'letrd',
             '%s <_ ( %s x. ( %s x. ( %s ^ J ) ) )' % (lhs0, eY, E, r))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21gterm']))
    return run(w)

def gen_geo():
    w = W('t21geo', 'The reflected geometric sum ` sum_ ( 0 <_ k <_ N ) R ^ ( N - k ) <_ 1 / ( 1 - R ) ` for ` 0 <_ R < 1 ` (Lean ` sum_geom_le ` with ` Finset.sum_range_reflect ` ; ~ fsumrev , ~ geoser ).')
    A0 = ante_of(S['t21geo'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    rr, r0, r1, nn = u['R e. RR'], u['0 <_ R'], u['R < 1'], u['N e. NN0']
    nz = st([nn], 'nn0zd', 'N e. ZZ'); nc = st([nz], 'zcnd', 'N e. CC')
    R0 = '( 0 ..^ ( N + 1 ) )'; F0 = '( 0 ... N )'
    fz = ap_(w, A0, [nz], 'fzval3', '%s = %s' % (F0, R0))
    BK = '( R ^ ( N - k ) )'
    s1 = st([st([fz], 'eqcomd', '%s = %s' % (R0, F0))], 'sumeq1d', 'sum_ k e. %s %s = sum_ k e. %s %s' % (R0, BK, F0, BK))
    C1 = '( %s /\\ k e. %s )' % (A0, F0)
    kc = w.s([_cl.lift(w, rr, C1), ap_(w, C1, [w.s([], 'simpr', '( %s -> k e. %s )' % (C1, F0))], 'fznn0sub', '( N - k ) e. NN0')], 'reexpcld', '( %s -> %s e. RR )' % (C1, BK))
    BJ = '( R ^ ( N - ( N - j ) ) )'
    sb = w.s([w.s([], 'oveq2', '( k = ( N - j ) -> ( N - k ) = ( N - ( N - j ) ) )')], 'oveq2d', '( k = ( N - j ) -> %s = %s )' % (BK, BJ))
    zz = st([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ')
    s2 = st([nz, zz, nz, w.s([kc], 'recnd', '( %s -> %s e. CC )' % (C1, BK)), sb], 'fsumrev', 'sum_ k e. %s %s = sum_ j e. ( ( N - N ) ... ( N - 0 ) ) %s' % (F0, BK, BJ))
    rg = st([st([nc], 'subidd', '( N - N ) = 0'), st([nc], 'subid1d', '( N - 0 ) = N')], 'oveq12d', '( ( N - N ) ... ( N - 0 ) ) = %s' % F0)
    s3 = st([rg], 'sumeq1d', 'sum_ j e. ( ( N - N ) ... ( N - 0 ) ) %s = sum_ j e. %s %s' % (BJ, F0, BJ))
    C2 = '( %s /\\ j e. %s )' % (A0, F0)
    jz = ap_(w, C2, [w.s([], 'simpr', '( %s -> j e. %s )' % (C2, F0))], 'elfzelz', 'j e. ZZ')
    nn2 = w.s([_cl.lift(w, nc, C2), w.s([jz], 'zcnd', '( %s -> j e. CC )' % C2)], 'nncand', '( %s -> ( N - ( N - j ) ) = j )' % C2)
    s4 = st([w.s([nn2], 'oveq2d', '( %s -> %s = ( R ^ j ) )' % (C2, BJ))], 'sumeq2dv', 'sum_ j e. %s %s = sum_ j e. %s ( R ^ j )' % (F0, BJ, F0))
    cb = w.s([w.s([], 'oveq2', '( j = k -> ( R ^ j ) = ( R ^ k ) )')], 'cbvsumv', 'sum_ j e. %s ( R ^ j ) = sum_ k e. %s ( R ^ k )' % (F0, F0))
    N1 = '( N + 1 )'
    pn = st([nc, st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'pncand', '( %s - 1 ) = N' % N1)
    gs = st([st([rr], 'recnd', 'R e. CC'), st([rr, r1], 'ltned', 'R =/= 1'), ap_(w, A0, [nn], 'peano2nn0', '%s e. NN0' % N1)], 'geoser',
            'sum_ k e. ( 0 ... ( %s - 1 ) ) ( R ^ k ) = ( ( 1 - ( R ^ %s ) ) / ( 1 - R ) )' % (N1, N1))
    gs2 = st([st([st([pn], 'oveq2d', '( 0 ... ( %s - 1 ) ) = %s' % (N1, F0))], 'sumeq1d', 'sum_ k e. ( 0 ... ( %s - 1 ) ) ( R ^ k ) = sum_ k e. %s ( R ^ k )' % (N1, F0)), gs], 'eqtr3d',
             'sum_ k e. %s ( R ^ k ) = ( ( 1 - ( R ^ %s ) ) / ( 1 - R ) )' % (F0, N1))
    chain = st([s1, s2], 'eqtrd', 'sum_ k e. %s %s = sum_ j e. ( ( N - N ) ... ( N - 0 ) ) %s' % (R0, BK, BJ))
    chain = st([chain, s3], 'eqtrd', 'sum_ k e. %s %s = sum_ j e. %s %s' % (R0, BK, F0, BJ))
    chain = st([chain, s4], 'eqtrd', 'sum_ k e. %s %s = sum_ j e. %s ( R ^ j )' % (R0, BK, F0))
    chain = st([chain, st([cb], 'a1i', 'sum_ j e. %s ( R ^ j ) = sum_ k e. %s ( R ^ k )' % (F0, F0))], 'eqtrd', 'sum_ k e. %s %s = sum_ k e. %s ( R ^ k )' % (R0, BK, F0))
    chain = st([chain, gs2], 'eqtrd', 'sum_ k e. %s %s = ( ( 1 - ( R ^ %s ) ) / ( 1 - R ) )' % (R0, BK, N1))
    rn = st([rr, ap_(w, A0, [nn], 'peano2nn0', '%s e. NN0' % N1)], 'reexpcld', '( R ^ %s ) e. RR' % N1)
    rn0 = st([rr, ap_(w, A0, [nn], 'peano2nn0', '%s e. NN0' % N1), r0], 'expge0d', '0 <_ ( R ^ %s )' % N1)
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    om = st([st([one, rr], 'resubcld', '( 1 - R ) e. RR'), st([rr, one], 'x', 'x') if False else lin.linarith(w, A0, [r1], '0 < ( 1 - R )', leaves={'R': rr})], 'elrpd', '( 1 - R ) e. RR+')
    nm = lin.linarith(w, A0, [rn0], '( 1 - ( R ^ %s ) ) <_ 1' % N1, leaves={'( R ^ %s )' % N1: rn})
    dv = st([st([one, rn], 'resubcld', '( 1 - ( R ^ %s ) ) e. RR' % N1), one, om, nm], 'lediv1dd', '( ( 1 - ( R ^ %s ) ) / ( 1 - R ) ) <_ ( 1 / ( 1 - R ) )' % N1)
    fin = st([chain, dv], 'eqbrtrd', 'sum_ k e. %s %s <_ ( 1 / ( 1 - R ) )' % (R0, BK))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21geo']))
    return run(w)

def gen_ggeo():
    w = W('t21ggeo', 'Geometric bound along the grid: with ` h = 1 / log X ` and ` M = floor ( ( T - S ) log X ) + 1 ` , ` sum_ ( k < M ) Y ^ ( S + ( k + 1 ) h ) D ^ ( ( 9 / 2 ) ( 1 - S - k h ) ) <_ 64 Y X ^ ( - ( 9 / 200 ) ( 1 - T ) ) ` (Lean ` grid_geom ` ; ~ t21gterm , ~ t21geo , ~ t21e272 , ~ t21e9 ).')
    A0 = ante_of(S['t21ggeo'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    L = LX; h = LH; E = EXPT; r = RR9
    xr, xe, yr, y1, yx, dr, d1, dy, sr, tr, sT, t1 = [u[k] for k in ['X e. RR', '( exp ` 1 ) <_ X', 'Y e. RR', '1 <_ Y', 'Y <_ X', 'D e. RR', '1 <_ D',
        '( D ^c %s ) <_ ( ( X ^c -u %s ) x. Y )' % (F92, F9200), 'S e. RR', 'T e. RR', 'S <_ T', 'T <_ 1']]
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    e1p = st([one], 'rpefcld', '( exp ` 1 ) e. RR+'); e1r = st([e1p], 'rpred', '( exp ` 1 ) e. RR')
    xp = st([xr, lin.linarith(w, A0, [st([e1p], 'rpgt0d', '0 < ( exp ` 1 )'), xe], '0 < X', leaves={'X': xr, '( exp ` 1 )': e1r})], 'elrpd', 'X e. RR+')
    lge = st([xe, st([e1p, xp], 'logled', '( ( exp ` 1 ) <_ X <-> ( log ` ( exp ` 1 ) ) <_ %s )' % L)], 'mpbid', '( log ` ( exp ` 1 ) ) <_ %s' % L)
    l1 = st([st([ap_(w, A0, [one], 'relogef', '( log ` ( exp ` 1 ) ) = 1')], 'eqcomd', '1 = ( log ` ( exp ` 1 ) )'), lge], 'eqbrtrd', '1 <_ %s' % L)
    lr = st([xp], 'relogcld', '%s e. RR' % L)
    lp = st([lr, lin.linarith(w, A0, [l1], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    TSL = '( ( T - S ) x. %s )' % L
    tsr = st([tr, sr], 'resubcld', '( T - S ) e. RR')
    ts0 = st([sT, st([tr, sr], 'subge0d', '( 0 <_ ( T - S ) <-> S <_ T )')], 'mpbird', '0 <_ ( T - S )')
    tslr = st([tsr, lr], 'remulcld', '%s e. RR' % TSL)
    tsl0 = st([tsr, lr, ts0, st([lp], 'rpge0d', '0 <_ %s' % L)], 'mulge0d', '0 <_ %s' % TSL)
    NF = '( |_ ` %s )' % TSL
    nf = ap_(w, A0, [tslr, tsl0], 'flge0nn0', '%s e. NN0' % NF)
    nfle = ap_(w, A0, [tslr], 'flle', '%s <_ %s' % (NF, TSL))
    MG_ = '( %s + 1 )' % NF
    FZ = '( 0 ..^ %s )' % MG_
    Ck = '( %s /\\ k e. %s )' % (A0, FZ)
    Lk = lambda s_: _cl.lift(w, s_, Ck)
    kin = w.s([], 'simpr', '( %s -> k e. %s )' % (Ck, FZ))
    kn = ap_(w, Ck, [kin], 'elfzonn0', 'k e. NN0')
    kz = w.s([kn], 'nn0zd', '( %s -> k e. ZZ )' % Ck); kr = w.s([kn], 'nn0red', '( %s -> k e. RR )' % Ck)
    nfz = Lk(st([nf], 'nn0zd', '%s e. ZZ' % NF))
    klt = ap_(w, Ck, [kin], 'elfzolt2', 'k < %s' % MG_)
    kle = w.s([klt, ap_(w, Ck, [kz, nfz], 'zleltp1', '( k <_ %s <-> k < %s )' % (NF, MG_))], 'mpbird', '( %s -> k <_ %s )' % (Ck, NF))
    J = '( %s - k )' % NF
    jn = w.s([kle, ap_(w, Ck, [kz, nfz], 'znn0sub', '( k <_ %s <-> %s e. NN0 )' % (NF, J))], 'mpbid', '( %s -> %s e. NN0 )' % (Ck, J))
    nfr = w.s([nfz], 'zred', '( %s -> %s e. RR )' % (Ck, NF))
    ktsl = w.s([kr, nfr, Lk(tslr), kle, Lk(nfle)], 'letrd', '( %s -> k <_ %s )' % (Ck, TSL))
    kd = w.s([ktsl, w.s([kr, Lk(tsr), Lk(lp)], 'ledivmul2d', '( %s -> ( ( k / %s ) <_ ( T - S ) <-> k <_ %s ) )' % (Ck, L, TSL))], 'mpbird', '( %s -> ( k / %s ) <_ ( T - S ) )' % (Ck, L))
    kh = w.s([w.s([kr], 'recnd', '( %s -> k e. CC )' % Ck), Lk(st([lp], 'rpcnd', '%s e. CC' % L)), Lk(st([lp], 'rpne0d', '%s =/= 0' % L))], 'divrecd', '( %s -> ( k / %s ) = ( k x. %s ) )' % (Ck, L, h))
    kd2 = w.s([kh, kd], 'eqbrtrrd', '( %s -> ( k x. %s ) <_ ( T - S ) )' % (Ck, h))
    KH = '( k x. %s )' % h
    khr = w.s([kr, Lk(st([st([lp], 'rpreccld', '%s e. RR+' % h)], 'rpred', '%s e. RR' % h))], 'remulcld', '( %s -> %s e. RR )' % (Ck, KH))
    sg = lin.linarith(w, Ck, [kd2], '( S + %s ) <_ T' % KH, leaves={'S': Lk(sr), 'T': Lk(tr), KH: khr})
    jk = w.s([w.s([w.s([nfz], 'zcnd', '( %s -> %s e. CC )' % (Ck, NF)), w.s([kr], 'recnd', '( %s -> k e. CC )' % Ck)], 'npcand', '( %s -> ( %s + k ) = %s )' % (Ck, J, NF)), Lk(nfle)], 'eqbrtrd', '( %s -> ( %s + k ) <_ %s )' % (Ck, J, TSL))
    TERMF = '( ( Y ^c ( S + ( ( k + 1 ) x. %s ) ) ) x. ( D ^c ( %s x. ( 1 - ( S + ( k x. %s ) ) ) ) ) )' % (h, F92, h)
    eY = '( ( exp ` 1 ) x. Y )'
    BD = '( %s x. ( %s x. ( %s ^ %s ) ) )' % (eY, E, r, J)
    tm = ap_(w, Ck, [Lk(xr), Lk(xe), Lk(yr), Lk(y1), Lk(yx), Lk(dr), Lk(d1), Lk(dy), Lk(sr), Lk(tr), Lk(t1), jn, kr, sg, jk], 't21gterm', '%s <_ %s' % (TERMF, BD))
    # reals under Ck
    ylk = Lk(st([yr, lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr})], 'jca', '( Y e. RR /\\ 0 <_ Y )'))
    y0 = lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr})
    hr = st([st([lp], 'rpreccld', '%s e. RR+' % h)], 'rpred', '%s e. RR' % h)
    e1_ = w.s([Lk(sr), w.s([ap_(w, Ck, [kr], 'peano2re', '( k + 1 ) e. RR'), Lk(hr)], 'remulcld', '( %s -> ( ( k + 1 ) x. %s ) e. RR )' % (Ck, h))], 'readdcld', '( %s -> ( S + ( ( k + 1 ) x. %s ) ) e. RR )' % (Ck, h))
    y_ = w.s([Lk(yr), Lk(y0), e1_], 'recxpcld', '( %s -> ( Y ^c ( S + ( ( k + 1 ) x. %s ) ) ) e. RR )' % (Ck, h))
    om_ = w.s([w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Ck), w.s([Lk(sr), khr], 'readdcld', '( %s -> ( S + %s ) e. RR )' % (Ck, KH))], 'resubcld', '( %s -> ( 1 - ( S + %s ) ) e. RR )' % (Ck, KH))], 'x', 'x') if False else w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Ck), w.s([Lk(sr), khr], 'readdcld', '( %s -> ( S + %s ) e. RR )' % (Ck, KH))], 'resubcld', '( %s -> ( 1 - ( S + %s ) ) e. RR )' % (Ck, KH))
    d0 = lin.linarith(w, A0, [d1], '0 <_ D', leaves={'D': dr})
    dd_ = w.s([Lk(dr), Lk(d0), w.s([w.s([num.real(w, F92)], 'a1i', '( %s -> %s e. RR )' % (Ck, F92)), om_], 'remulcld', '( %s -> ( %s x. ( 1 - ( S + %s ) ) ) e. RR )' % (Ck, F92, KH))], 'recxpcld',
              '( %s -> ( D ^c ( %s x. ( 1 - ( S + %s ) ) ) ) e. RR )' % (Ck, F92, KH))
    termr = w.s([y_, dd_], 'remulcld', '( %s -> %s e. RR )' % (Ck, TERMF))
    e9r = st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200)
    rr_ = st([e9r], 'reefcld', '%s e. RR' % r); rp_ = st([e9r], 'rpefcld', '%s e. RR+' % r)
    RJ = '( %s ^ %s )' % (r, J)
    rjr = w.s([Lk(rr_), jn], 'reexpcld', '( %s -> %s e. RR )' % (Ck, RJ))
    ep = st([xp, st([e9r, st([one, tr], 'resubcld', '( 1 - T ) e. RR')], 'remulcld', '( -u %s x. ( 1 - T ) ) e. RR' % F9200)], 'rpcxpcld', '%s e. RR+' % E)
    er_ = st([ep], 'rpred', '%s e. RR' % E)
    eyr = st([e1r, yr], 'remulcld', '%s e. RR' % eY)
    ERJ = '( %s x. %s )' % (E, RJ)
    erj = w.s([Lk(er_), rjr], 'remulcld', '( %s -> %s e. RR )' % (Ck, ERJ))
    bdr = w.s([Lk(eyr), erj], 'remulcld', '( %s -> %s e. RR )' % (Ck, BD))
    fz = st([w.s([], 'fzofi', '%s e. Fin' % FZ)], 'a1i', '%s e. Fin' % FZ)
    SUMT = 'sum_ k e. %s %s' % (FZ, TERMF)
    s1 = st([fz, termr, bdr, tm], 'fsumle', '%s <_ sum_ k e. %s %s' % (SUMT, FZ, BD))
    s2 = st([fz, st([eyr], 'recnd', '%s e. CC' % eY), w.s([erj], 'recnd', '( %s -> %s e. CC )' % (Ck, ERJ))], 'fsummulc2', '( %s x. sum_ k e. %s %s ) = sum_ k e. %s %s' % (eY, FZ, ERJ, FZ, BD))
    G = 'sum_ k e. %s %s' % (FZ, RJ)
    s3 = st([fz, st([er_], 'recnd', '%s e. CC' % E), w.s([rjr], 'recnd', '( %s -> %s e. CC )' % (Ck, RJ))], 'fsummulc2', '( %s x. %s ) = sum_ k e. %s %s' % (E, G, FZ, ERJ))
    # G <_ 209 / 9
    e9 = st([w.s([], 't21e9', '%s <_ ( ; ; 2 0 0 / ; ; 2 0 9 )' % r)], 'a1i', '%s <_ ( ; ; 2 0 0 / ; ; 2 0 9 )' % r)
    c0 = _cl.Closure(w, A0, {})
    c0.leaf(r, 'RR', rr_)
    r1_ = lin.linarith(w, A0, [e9], '%s < 1' % r, closure=c0)
    gg = ap_(w, A0, [rr_, st([rp_], 'rpge0d', '0 <_ %s' % r), r1_, nf], 't21geo', '%s <_ ( 1 / ( 1 - %s ) )' % (G, r))
    q9 = '( 9 / ; ; 2 0 9 )'
    om = st([st([one, rr_], 'resubcld', '( 1 - %s ) e. RR' % r), lin.linarith(w, A0, [r1_], '0 < ( 1 - %s )' % r, closure=c0)], 'elrpd', '( 1 - %s ) e. RR+' % r)
    q9le = lin.linarith(w, A0, [e9], '%s <_ ( 1 - %s )' % (q9, r), closure=c0)
    q9p = st([num.rp(w, q9)], 'a1i', '%s e. RR+' % q9)
    rc = st([q9le, st([q9p, om], 'lerecd', '( %s <_ ( 1 - %s ) <-> ( 1 / ( 1 - %s ) ) <_ ( 1 / %s ) )' % (q9, r, r, q9))], 'mpbid', '( 1 / ( 1 - %s ) ) <_ ( 1 / %s )' % (r, q9))
    rd = st([st([num.cc(w, '9')], 'a1i', '9 e. CC'), st([num.cc(w, '; ; 2 0 9')], 'a1i', '; ; 2 0 9 e. CC'), st([num.ne0_nat(w, 9)], 'a1i', '9 =/= 0'), st([num.ne0_nat(w, 209)], 'a1i', '; ; 2 0 9 =/= 0')], 'recdivd', '( 1 / %s ) = ( ; ; 2 0 9 / 9 )' % q9)
    gr = st([fz, rjr], 'fsumrecl', '%s e. RR' % G)
    g0 = st([fz, rjr, w.s([Lk(rr_), jn, Lk(st([rp_], 'rpge0d', '0 <_ %s' % r))], 'expge0d', '( %s -> 0 <_ %s )' % (Ck, RJ))], 'fsumge0', '0 <_ %s' % G)
    gle = st([gr, st([om], 'rpreccld', '( 1 / ( 1 - %s ) ) e. RR+' % r) and st([st([om], 'rpreccld', '( 1 / ( 1 - %s ) ) e. RR+' % r)], 'rpred', '( 1 / ( 1 - %s ) ) e. RR' % r), st([num.real(w, '( ; ; 2 0 9 / 9 )')], 'a1i', '( ; ; 2 0 9 / 9 ) e. RR'), gg, st([rc, rd], 'breqtrd', '( 1 / ( 1 - %s ) ) <_ ( ; ; 2 0 9 / 9 )' % r)], 'letrd', '%s <_ ( ; ; 2 0 9 / 9 )' % G)
    ee = st([w.s([], 't21e272', '( exp ` 1 ) <_ ( ; 6 8 / ; 2 5 )')], 'a1i', '( exp ` 1 ) <_ ( ; 6 8 / ; 2 5 )')
    eg = st([e1r, st([num.real(w, '( ; 6 8 / ; 2 5 )')], 'a1i', '( ; 6 8 / ; 2 5 ) e. RR'), gr, st([num.real(w, '( ; ; 2 0 9 / 9 )')], 'a1i', '( ; ; 2 0 9 / 9 ) e. RR'), st([e1p], 'rpge0d', '0 <_ ( exp ` 1 )'), g0, ee, gle], 'lemul12ad',
            '( ( exp ` 1 ) x. %s ) <_ ( ( ; 6 8 / ; 2 5 ) x. ( ; ; 2 0 9 / 9 ) )' % G)
    ml = st([num.mul_lits(w, '( ; 6 8 / ; 2 5 )', '( ; ; 2 0 9 / 9 )')], 'a1i', '( ( ; 6 8 / ; 2 5 ) x. ( ; ; 2 0 9 / 9 ) ) = %s' % num.lit_text(__import__('fractions').Fraction(68, 25) * __import__('fractions').Fraction(209, 9)))
    lit = num.lit_text(__import__('fractions').Fraction(68, 25) * __import__('fractions').Fraction(209, 9))
    l64 = st([num.le_lit(w, lit, '; 6 4')], 'a1i', '%s <_ ; 6 4' % lit)
    eG = '( ( exp ` 1 ) x. %s )' % G
    eg64 = st([st([eg, ml], 'breqtrd', '%s <_ %s' % (eG, lit)), l64], 'x', 'x') if False else st([st([e1r, gr], 'remulcld', '%s e. RR' % eG), st([num.real(w, lit)], 'a1i', '%s e. RR' % lit), st([num.real(w, '; 6 4')], 'a1i', '; 6 4 e. RR'), st([eg, ml], 'breqtrd', '%s <_ %s' % (eG, lit)), l64], 'letrd', '%s <_ ; 6 4' % eG)
    # rearrangement
    YE = '( Y x. %s )' % E
    yer = st([yr, er_], 'remulcld', '%s e. RR' % YE); ye0 = st([yr, er_, y0, st([ep], 'rpge0d', '0 <_ %s' % E)], 'mulge0d', '0 <_ %s' % YE)
    f1 = st([st([eG and e1r], 'x', 'x') if False else st([e1r, gr], 'remulcld', '%s e. RR' % eG), st([num.real(w, '; 6 4')], 'a1i', '; 6 4 e. RR'), yer, ye0, eg64], 'lemul1ad', '( %s x. %s ) <_ ( ; 6 4 x. %s )' % (eG, YE, YE))
    cc_ = lambda s_, E_: st([s_], 'recnd', '%s e. CC' % E_)
    r1 = st([st([cc_(er_, E), cc_(gr, G)], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (E, G, G, E))], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (eY, E, G, eY, G, E))
    r2 = st([cc_(e1r, '( exp ` 1 )'), cc_(yr, 'Y'), cc_(gr, G), cc_(er_, E)], 'mul4d', '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (eY, G, E, eG, YE))
    r3 = st([st([num.cc(w, '; 6 4')], 'a1i', '; 6 4 e. CC'), cc_(yr, 'Y'), cc_(er_, E)], 'mulassd', '( ( ; 6 4 x. Y ) x. %s ) = ( ; 6 4 x. %s )' % (E, YE))
    lhsE = '( %s x. ( %s x. %s ) )' % (eY, E, G)
    f2 = st([st([st([r1, r2], 'eqtrd', '%s = ( %s x. %s )' % (lhsE, eG, YE)), f1], 'eqbrtrd', '%s <_ ( ; 6 4 x. %s )' % (lhsE, YE)), r3], 'breqtrrd', '%s <_ ( ( ; 6 4 x. Y ) x. %s )' % (lhsE, E))
    SBD = 'sum_ k e. %s %s' % (FZ, BD)
    s23 = st([st([s2], 'eqcomd', '%s = ( %s x. sum_ k e. %s %s )' % (SBD, eY, FZ, ERJ)), st([st([s3], 'eqcomd', 'sum_ k e. %s %s = ( %s x. %s )' % (FZ, ERJ, E, G))], 'oveq2d', '( %s x. sum_ k e. %s %s ) = %s' % (eY, FZ, ERJ, lhsE))], 'eqtrd', '%s = %s' % (SBD, lhsE))
    sbr = st([fz, bdr], 'fsumrecl', '%s e. RR' % SBD)
    fin = st([st([fz, termr], 'fsumrecl', '%s e. RR' % SUMT), sbr, st([st([st([num.real(w, '; 6 4')], 'a1i', '; 6 4 e. RR'), yr], 'remulcld', '( ; 6 4 x. Y ) e. RR'), er_], 'remulcld', '( ( ; 6 4 x. Y ) x. %s ) e. RR' % E),
              s1, st([s23, f2], 'eqbrtrd', '%s <_ ( ( ; 6 4 x. Y ) x. %s )' % (SBD, E))], 'letrd', '%s <_ ( ( ; 6 4 x. Y ) x. %s )' % (SUMT, E))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21ggeo']))
    return run(w)

def gen_gz():
    pass


if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21gridr', gen_gridr), ('t21grid', gen_grid), ('t21gterm', gen_gterm), ('t21geo', gen_geo), ('t21ggeo', gen_ggeo)]:
        if not only or lab in only:
            f()
