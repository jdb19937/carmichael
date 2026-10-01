"""Sortie Z4b, section A: the exponential e ( nu t ) as a function of t
(LargeSieve continuous_eAt, hasDerivAt_eAt, integral_eAt) and the generic
interval-integration tools (integrability of a continuous mapping on an open
interval; the fundamental theorem for an everywhere differentiable function)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z4blib import *
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


EV = EAT('V', 't')
IN = '( %s x. ( V x. t ) )' % C2
MAPE = '( t e. RR |-> %s )' % EV

# ---- eatdv
if __name__ == '__main__':
    A0 = 'V e. CC'; At = '( V e. CC /\\ t e. RR )'
    w = W('eatdv', 'The derivative of t |-> e ( V t ) = exp ( 2 pi i V t ) is 2 pi i V e ( V t ) (LargeSieve hasDerivAt_eAt).')
    v = w.s([], 'id', '( V e. CC -> V e. CC )')
    rr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }'); cc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    did = st(w, A0, [rr], 'dvmptid', '( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 )')
    tr = w.s([], 'simpr', '( %s -> t e. RR )' % At); tc = st(w, At, [tr], 'recnd', 't e. CC')
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % At)
    d1 = st(w, A0, [rr, tc, one, did, v], 'dvmptcmul', '( RR _D ( t e. RR |-> ( V x. t ) ) ) = ( t e. RR |-> ( V x. 1 ) )')
    vt = lift(w, v, At)
    vtc = st(w, At, [vt, tc], 'mulcld', '( V x. t ) e. CC'); v1c = st(w, At, [vt, one], 'mulcld', '( V x. 1 ) e. CC')
    c2 = c2cl(w, A0)
    d2 = st(w, A0, [rr, vtc, v1c, d1, c2], 'dvmptcmul', '( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( %s x. ( V x. 1 ) ) )' % (IN, C2))
    c2t = lift(w, c2, At)
    inc = st(w, At, [c2t, vtc], 'mulcld', '%s e. CC' % IN); bc = st(w, At, [c2t, v1c], 'mulcld', '( %s x. ( V x. 1 ) ) e. CC' % C2)
    Ay = '( V e. CC /\\ y e. CC )'
    ey = st(w, Ay, [w.s([], 'simpr', '( %s -> y e. CC )' % Ay)], 'efcld', '( exp ` y ) e. CC')
    ef = a1(w, A0, 'eff', 'exp : CC --> CC')
    fm = st(w, A0, [ef], 'feqmptd', 'exp = ( y e. CC |-> ( exp ` y ) )')
    de = a1(w, A0, 'dvef', '( CC _D exp ) = exp')
    fm2 = st(w, A0, [eqc(w, A0, fm)], 'oveq2d', '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( CC _D exp )')
    dexp = eqt(w, A0, eqt(w, A0, fm2, de), fm)
    e = w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = ( exp ` %s ) )' % (IN, IN))
    co = st(w, A0, [rr, cc, inc, bc, ey, ey, d2, dexp, e, e], 'dvmptco', '( RR _D %s ) = ( t e. RR |-> ( %s x. ( %s x. ( V x. 1 ) ) ) )' % (MAPE, EV, C2))
    r1 = st(w, At, [st(w, At, [vt], 'mulridd', '( V x. 1 ) = V')], 'oveq2d', '( %s x. ( V x. 1 ) ) = ( %s x. V )' % (C2, C2))
    r2 = st(w, At, [r1], 'oveq2d', '( %s x. ( %s x. ( V x. 1 ) ) ) = ( %s x. ( %s x. V ) )' % (EV, C2, EV, C2))
    evc = st(w, At, [inc], 'efcld', '%s e. CC' % EV)
    r3 = st(w, At, [evc, st(w, At, [c2t, vt], 'mulcld', '( %s x. V ) e. CC' % C2)], 'mulcomd', '( %s x. ( %s x. V ) ) = ( ( %s x. V ) x. %s )' % (EV, C2, C2, EV))
    mp = st(w, A0, [eqt(w, At, r2, r3)], 'mpteq2dva', '( t e. RR |-> ( %s x. ( %s x. ( V x. 1 ) ) ) ) = ( t e. RR |-> ( ( %s x. V ) x. %s ) )' % (EV, C2, C2, EV))
    w.qed([co, mp], 'eqtrd', STATEMENTS['eatdv']); go(w)

# ---- eatcn
if __name__ == '__main__':
    A0 = 'V e. CC'; At = '( V e. CC /\\ t e. RR )'
    w = W('eatcn', 'The function t |-> e ( V t ) is continuous on RR (LargeSieve continuous_eAt).')
    v = w.s([], 'id', '( V e. CC -> V e. CC )'); vt = lift(w, v, At)
    tc = st(w, At, [w.s([], 'simpr', '( %s -> t e. RR )' % At)], 'recnd', 't e. CC')
    evc = ap(w, At, 'eatcl', [vt, tc], '%s e. CC' % EV)
    fm = st(w, A0, [evc], 'fmptd', '%s : RR --> CC' % MAPE)
    K = '( %s x. V )' % C2
    dv = ap(w, A0, 'eatdv', [v], '( RR _D %s ) = ( t e. RR |-> ( %s x. %s ) )' % (MAPE, K, EV))
    kc = st(w, At, [st(w, At, [lift(w, c2cl(w, A0), At), vt], 'mulcld', '%s e. CC' % K), evc], 'mulcld', '( %s x. %s ) e. CC' % (K, EV))
    ral = st(w, A0, [kc], 'ralrimiva', 'A. t e. RR ( %s x. %s ) e. CC' % (K, EV))
    dm = ap(w, A0, 'dmmptg', [ral], 'dom ( t e. RR |-> ( %s x. %s ) ) = RR' % (K, EV))
    dm2 = st(w, A0, [dv], 'dmeqd', 'dom ( RR _D %s ) = dom ( t e. RR |-> ( %s x. %s ) )' % (MAPE, K, EV))
    dmr = eqt(w, A0, dm2, dm)
    j3 = J(w, A0, a1(w, A0, 'ax-resscn', 'RR C_ CC'), fm, a1(w, A0, 'ssid', 'RR C_ RR'))
    w.qed([J(w, A0, j3, dmr), w.inst('dvcn')], 'syl', STATEMENTS['eatcn']); go(w)

# ---- eatcj
if __name__ == '__main__':
    A0 = '( V e. RR /\\ B e. RR )'
    w = W('eatcj', 'The conjugate of e ( V B ) for real V, B is e ( -u V B ).')
    vr = w.s([], 'simpl', '( %s -> V e. RR )' % A0); br = w.s([], 'simpr', '( %s -> B e. RR )' % A0)
    vc = st(w, A0, [vr], 'recnd', 'V e. CC'); bc = st(w, A0, [br], 'recnd', 'B e. CC')
    VB = '( V x. B )'; TP = '( 2 x. _pi )'; Z = '( %s x. %s )' % (C2, VB); R = '( %s x. %s )' % (TP, VB)
    two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0); ic = a1(w, A0, 'ax-icn', '_i e. CC'); pc = a1(w, A0, 'picn', '_pi e. CC')
    vb = st(w, A0, [vc, bc], 'mulcld', '%s e. CC' % VB); vbr = st(w, A0, [vr, br], 'remulcld', '%s e. RR' % VB)
    e1 = st(w, A0, [two, ic, pc], 'mul12d', '%s = ( _i x. %s )' % (C2, TP))
    e2 = st(w, A0, [e1], 'oveq1d', '%s = ( ( _i x. %s ) x. %s )' % (Z, TP, VB))
    tpc = st(w, A0, [two, pc], 'mulcld', '%s e. CC' % TP)
    e3 = st(w, A0, [ic, tpc, vb], 'mulassd', '( ( _i x. %s ) x. %s ) = ( _i x. %s )' % (TP, VB, R))
    z1 = eqt(w, A0, e2, e3)
    tpr = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], 'pire', '_pi e. RR')], 'remulcli', '%s e. RR' % TP)], 'a1i', '( %s -> %s e. RR )' % (A0, TP))
    rr = st(w, A0, [tpr, vbr], 'remulcld', '%s e. RR' % R); rc = st(w, A0, [rr], 'recnd', '%s e. CC' % R)
    cj1 = st(w, A0, [z1], 'fveq2d', '( * ` %s ) = ( * ` ( _i x. %s ) )' % (Z, R))
    cj2 = st(w, A0, [ic, rc], 'cjmuld', '( * ` ( _i x. %s ) ) = ( ( * ` _i ) x. ( * ` %s ) )' % (R, R))
    cj3 = st(w, A0, [rr], 'cjred', '( * ` %s ) = %s' % (R, R))
    cj4 = a1(w, A0, 'cji', '( * ` _i ) = -u _i')
    cj5 = st(w, A0, [cj4, cj3], 'oveq12d', '( ( * ` _i ) x. ( * ` %s ) ) = ( -u _i x. %s )' % (R, R))
    cj6 = st(w, A0, [ic, rc], 'mulneg1d', '( -u _i x. %s ) = -u ( _i x. %s )' % (R, R))
    cj7 = st(w, A0, [eqc(w, A0, z1)], 'negeqd', '-u ( _i x. %s ) = -u %s' % (R, Z))
    cjz = eqt(w, A0, eqt(w, A0, eqt(w, A0, eqt(w, A0, cj1, cj2), cj5), cj6), cj7)
    r1 = st(w, A0, [vc, bc], 'mulneg1d', '( -u V x. B ) = -u %s' % VB)
    r2 = st(w, A0, [r1], 'oveq2d', '( %s x. ( -u V x. B ) ) = ( %s x. -u %s )' % (C2, C2, VB))
    r3 = st(w, A0, [c2cl(w, A0), vb], 'mulneg2d', '( %s x. -u %s ) = -u %s' % (C2, VB, Z))
    r = eqt(w, A0, r2, r3)
    cjz2 = eqt(w, A0, cjz, r)
    zc = st(w, A0, [c2cl(w, A0), vb], 'mulcld', '%s e. CC' % Z)
    ex = ap(w, A0, 'efcj', [zc], '( exp ` ( * ` %s ) ) = ( * ` ( exp ` %s ) )' % (Z, Z))
    f = st(w, A0, [cjz2], 'fveq2d', '( exp ` ( * ` %s ) ) = %s' % (Z, EAT('-u V', 'B')))
    w.qed([ex, f], 'eqtr3d', STATEMENTS['eatcj']); go(w)

# ---- eatper
if __name__ == '__main__':
    A0 = '( V e. ZZ /\\ B e. CC )'
    w = W('eatper', 'The function t |-> e ( V t ) has period 1 for an integer frequency V.')
    vz = w.s([], 'simpl', '( %s -> V e. ZZ )' % A0); bc = w.s([], 'simpr', '( %s -> B e. CC )' % A0)
    vc = st(w, A0, [vz], 'zcnd', 'V e. CC'); one = w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)
    VB = '( V x. B )'; X = '( %s x. %s )' % (C2, VB); KI = '( ( _i x. ( 2 x. _pi ) ) x. V )'
    p1 = st(w, A0, [vc, bc, one], 'adddid', '( V x. ( B + 1 ) ) = ( %s + ( V x. 1 ) )' % VB)
    p3 = st(w, A0, [st(w, A0, [vc], 'mulridd', '( V x. 1 ) = V')], 'oveq2d', '( %s + ( V x. 1 ) ) = ( %s + V )' % (VB, VB))
    p5 = st(w, A0, [eqt(w, A0, p1, p3)], 'oveq2d', '( %s x. ( V x. ( B + 1 ) ) ) = ( %s x. ( %s + V ) )' % (C2, C2, VB))
    c2 = c2cl(w, A0); vbc = st(w, A0, [vc, bc], 'mulcld', '%s e. CC' % VB)
    p6 = st(w, A0, [c2, vbc, vc], 'adddid', '( %s x. ( %s + V ) ) = ( %s + ( %s x. V ) )' % (C2, VB, X, C2))
    p7 = st(w, A0, [w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), a1(w, A0, 'ax-icn', '_i e. CC'), a1(w, A0, 'picn', '_pi e. CC')], 'mul12d',
            '%s = ( _i x. ( 2 x. _pi ) )' % C2)
    p8 = st(w, A0, [p7], 'oveq1d', '( %s x. V ) = %s' % (C2, KI))
    p9 = st(w, A0, [p8], 'oveq2d', '( %s + ( %s x. V ) ) = ( %s + %s )' % (X, C2, X, KI))
    arg = eqt(w, A0, eqt(w, A0, p5, p6), p9)
    f1 = st(w, A0, [arg], 'fveq2d', '%s = ( exp ` ( %s + %s ) )' % (EAT('V', '( B + 1 )'), X, KI))
    xc = st(w, A0, [c2, vbc], 'mulcld', '%s e. CC' % X)
    f2 = ap(w, A0, 'efper', [xc, vz], '( exp ` ( %s + %s ) ) = ( exp ` %s )' % (X, KI, X))
    w.qed([f1, f2], 'eqtrd', STATEMENTS['eatper']); go(w)

# ---- lsibl
if __name__ == '__main__':
    w = W('lsibl', 'A mapping continuous on RR is integrable on every bounded open interval.')
    ha, hb, hc = hyps_of(w, 'lsibl')
    A0 = 'ph'
    ICCab = ICC('A', 'B'); MR = '( t e. RR |-> X )'; MI = '( t e. %s |-> X )' % ICCab
    ss = st(w, A0, [ha, hb], 'iccssred', '%s C_ RR' % ICCab)
    rs = ap(w, A0, 'resmpt', [ss], '( %s |` %s ) = %s' % (MR, ICCab, MI))
    rc = w.s([ss, hc, w.inst('rescncf')], 'sylc', '( ph -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (MR, ICCab, ICCab))
    mic = st(w, A0, [rs, rc], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (MI, ICCab))
    ib = ap(w, A0, 'cniccibl', [ha, hb, mic], '%s e. L^1' % MI)
    ff = ap(w, A0, 'cncff', [mic], '%s : %s --> CC' % (MI, ICCab))
    e = w.s([], 'eqid', '%s = %s' % (MI, MI))
    ral = w.s([ff, w.s([e], 'fmpt', '( A. t e. %s X e. CC <-> %s : %s --> CC )' % (ICCab, MI, ICCab))], 'sylibr', '( ph -> A. t e. %s X e. CC )' % ICCab)
    xc = w.s([ral], 'r19.21bi', '( ( ph /\\ t e. %s ) -> X e. CC )' % ICCab)
    sub = a1(w, A0, 'ioossicc', '%s C_ %s' % (IOO('A', 'B'), ICCab))
    dv = a1(w, A0, 'ioombl', '%s e. dom vol' % IOO('A', 'B'))
    w.qed([sub, dv, xc, ib], 'iblss', STATEMENTS['lsibl']); go(w)

# ---- lsftc
if __name__ == '__main__':
    AB = '( A e. RR /\\ B e. RR /\\ A <_ B )'
    A0 = '( %s /\\ %s )' % (AB, HF)
    w = W('lsftc', 'The fundamental theorem of calculus for a function differentiable on all of RR with a continuous derivative.')
    P = parts(w, A0)
    ar, br, le = P['A e. RR'], P['B e. RR'], P['A <_ B']
    ff, dfg, gcn = P['F : RR --> CC'], P['( RR _D F ) = G'], P['G e. %s' % CNR]
    I = ICC('A', 'B'); O = IOO('A', 'B'); FR = '( F |` %s )' % I; GR = '( G |` %s )' % O
    TOP = '( TopOpen ` CCfld )'; JR = '( %s |`t RR )' % TOP
    rcc = a1(w, A0, 'ax-resscn', 'RR C_ CC'); rrr = a1(w, A0, 'ssid', 'RR C_ RR')
    iss = st(w, A0, [ar, br], 'iccssred', '%s C_ RR' % I)
    k = w.s([], 'eqid', '%s = %s' % (TOP, TOP)); t = w.s([], 'eqid', '%s = %s' % (JR, JR))
    dres = w.s([J(w, A0, J(w, A0, rcc, ff), J(w, A0, rrr, iss)), w.s([k, t], 'dvres', '( ( ( RR C_ CC /\\ F : RR --> CC ) /\\ ( RR C_ RR /\\ %s C_ RR ) ) -> ( RR _D %s ) = ( ( RR _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (I, FR, JR, I))],
               'syl', '( %s -> ( RR _D %s ) = ( ( RR _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (A0, FR, JR, I))
    icc0 = ap(w, A0, 'iccntr', [ar, br], '( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s' % (I, O))
    tg = a1(w, A0, 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)
    tg1 = st(w, A0, [tg], 'fveq2d', '( int ` ( topGen ` ran (,) ) ) = ( int ` %s )' % JR)
    tg2 = st(w, A0, [tg1], 'fveq1d', '( ( int ` ( topGen ` ran (,) ) ) ` %s ) = ( ( int ` %s ) ` %s )' % (I, JR, I))
    ntr = eqt(w, A0, eqc(w, A0, tg2), icc0)
    dres2 = st(w, A0, [dfg, ntr], 'reseq12d', '( ( RR _D F ) |` ( ( int ` %s ) ` %s ) ) = %s' % (JR, I, GR))
    dfr = eqt(w, A0, dres, dres2)
    oss = a1(w, A0, 'ioossre', '%s C_ RR' % O)
    gcn2 = w.s([oss, gcn, w.inst('rescncf')], 'sylc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GR, O))
    dcn = st(w, A0, [dfr, gcn2], 'eqeltrd', '( RR _D %s ) e. ( %s -cn-> CC )' % (FR, O))
    # integrability of the derivative
    gf = ap(w, A0, 'cncff', [gcn], 'G : RR --> CC')
    GM = '( t e. RR |-> ( G ` t ) )'
    gm = st(w, A0, [gf], 'feqmptd', 'G = %s' % GM)
    gmc = st(w, A0, [gm, gcn], 'eqeltrrd', '%s e. %s' % (GM, CNR))
    ib = w.s([ar, br, gmc], 'lsibl', '( %s -> ( t e. %s |-> ( G ` t ) ) e. L^1 )' % (A0, O))
    gr = st(w, A0, [gm], 'reseq1d', '%s = ( %s |` %s )' % (GR, GM, O))
    gr2 = ap(w, A0, 'resmpt', [oss], '( %s |` %s ) = ( t e. %s |-> ( G ` t ) )' % (GM, O, O))
    grm = eqt(w, A0, gr, gr2)
    gib = st(w, A0, [eqt(w, A0, dfr, grm), ib], 'eqeltrd', '( RR _D %s ) e. L^1' % FR)
    # continuity of F on the closed interval
    dm = eqt(w, A0, st(w, A0, [dfg], 'dmeqd', 'dom ( RR _D F ) = dom G'), ap(w, A0, 'fdm', [gf], 'dom G = RR'))
    fcn = ap(w, A0, 'dvcn', [J(w, A0, J(w, A0, rcc, ff, rrr), dm)], 'F e. %s' % CNR)
    fcn2 = w.s([iss, fcn, w.inst('rescncf')], 'sylc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, FR, I))
    ftc = st(w, A0, [ar, br, le, dcn, gib, fcn2], 'ftc2', '%s = ( ( %s ` B ) - ( %s ` A ) )' % (ITG(O, '( ( RR _D %s ) ` t )' % FR), FR, FR))
    # the integrand and the end values
    At = '( %s /\\ t e. %s )' % (A0, O)
    tmem = w.s([], 'simpr', '( %s -> t e. %s )' % (At, O))
    v1 = st(w, At, [lift(w, dfr, At)], 'fveq1d', '( ( RR _D %s ) ` t ) = ( %s ` t )' % (FR, GR))
    v2 = ap(w, At, 'fvres', [tmem], '( %s ` t ) = ( G ` t )' % GR)
    itq = st(w, A0, [eqt(w, At, v1, v2)], 'itgeq2dv', '%s = %s' % (ITG(O, '( ( RR _D %s ) ` t )' % FR), ITG(O, '( G ` t )')))
    bm = ap(w, A0, 'ubicc2', [st(w, A0, [ar], 'rexrd', 'A e. RR*'), st(w, A0, [br], 'rexrd', 'B e. RR*'), le], 'B e. %s' % I)
    am = ap(w, A0, 'lbicc2', [st(w, A0, [ar], 'rexrd', 'A e. RR*'), st(w, A0, [br], 'rexrd', 'B e. RR*'), le], 'A e. %s' % I)
    fb = ap(w, A0, 'fvres', [bm], '( %s ` B ) = ( F ` B )' % FR); fa = ap(w, A0, 'fvres', [am], '( %s ` A ) = ( F ` A )' % FR)
    fd = st(w, A0, [fb, fa], 'oveq12d', '( ( %s ` B ) - ( %s ` A ) ) = ( ( F ` B ) - ( F ` A ) )' % (FR, FR))
    fin = eqt(w, A0, eqt(w, A0, eqc(w, A0, itq), ftc), fd)
    # rename the last step to qed
    last = w.lines.pop()
    w.lines.append('qed' + last[len(fin):])
    go(w)

# ---- eatitg
if __name__ == '__main__':
    A0 = '( V e. ZZ /\\ C e. RR )'
    w = W('eatitg', 'Period-1 orthogonality: the integral of e ( V t ) over a unit interval is 1 for V = 0 and 0 otherwise (LargeSieve integral_eAt).')
    vz = w.s([], 'simpl', '( %s -> V e. ZZ )' % A0); cr = w.s([], 'simpr', '( %s -> C e. RR )' % A0)
    vc = st(w, A0, [vz], 'zcnd', 'V e. CC')
    O = IOO('C', '( C + 1 )'); IT = ITG(O, EV)
    c1r = st(w, A0, [cr, w.s([], '1red', '( %s -> 1 e. RR )' % A0)], 'readdcld', '( C + 1 ) e. RR')
    cle = st(w, A0, [cr, c1r, st(w, A0, [cr], 'ltp1d', 'C < ( C + 1 )')], 'ltled', 'C <_ ( C + 1 )')
    # V = 0
    A1 = '( %s /\\ V = 0 )' % A0
    At1 = '( %s /\\ t e. %s )' % (A1, O)
    v0 = lift(w, w.s([], 'simpr', '( %s -> V = 0 )' % A1), At1)
    tr = ap(w, At1, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (At1, O))], 't e. RR'); tc = st(w, At1, [tr], 'recnd', 't e. CC')
    e3 = eqt(w, At1, st(w, At1, [v0], 'oveq1d', '( V x. t ) = ( 0 x. t )'), st(w, At1, [tc], 'mul02d', '( 0 x. t ) = 0'))
    e4 = eqt(w, At1, st(w, At1, [e3], 'oveq2d', '( %s x. ( V x. t ) ) = ( %s x. 0 )' % (C2, C2)), st(w, At1, [c2cl(w, At1)], 'mul01d', '( %s x. 0 ) = 0' % C2))
    e8 = eqt(w, At1, st(w, At1, [e4], 'fveq2d', '%s = ( exp ` 0 )' % EV), a1(w, At1, 'ef0', '( exp ` 0 ) = 1'))
    i1 = st(w, A1, [e8], 'itgeq2dv', '%s = %s' % (IT, ITG(O, '1')))
    L1 = lambda s_: lift(w, s_, A1)
    vo = ap(w, A1, 'volioo', [L1(cr), L1(c1r), L1(cle)], '( vol ` %s ) = ( ( C + 1 ) - C )' % O)
    vs = st(w, A1, [st(w, A1, [L1(cr)], 'recnd', 'C e. CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % A1)], 'pncan2d', '( ( C + 1 ) - C ) = 1')
    v1 = eqt(w, A1, vo, vs)
    vr = st(w, A1, [v1, w.s([], '1red', '( %s -> 1 e. RR )' % A1)], 'eqeltrd', '( vol ` %s ) e. RR' % O)
    i2 = ap(w, A1, 'itgconst', [a1(w, A1, 'ioombl', '%s e. dom vol' % O), vr, w.s([], '1cnd', '( %s -> 1 e. CC )' % A1)], '%s = ( 1 x. ( vol ` %s ) )' % (ITG(O, '1'), O))
    i3 = eqt(w, A1, st(w, A1, [v1], 'oveq2d', '( 1 x. ( vol ` %s ) ) = ( 1 x. 1 )' % O), a1(w, A1, '1t1e1', '( 1 x. 1 ) = 1'))
    case1 = eqc(w, A1, eqt(w, A1, eqt(w, A1, i1, i2), i3))
    # V =/= 0
    A2 = '( %s /\\ -. V = 0 )' % A0
    L2 = lambda s_: lift(w, s_, A2)
    K = '( %s x. V )' % C2
    vc2 = L2(vc)
    vne = st(w, A2, [w.s([], 'simpr', '( %s -> -. V = 0 )' % A2)], 'neqned', 'V =/= 0')
    c2ne = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'),
                     w.s([], '2ne0', '2 =/= 0'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( _i x. _pi ) =/= 0')],
                    'mulne0i', '%s =/= 0' % C2)], 'a1i', '( %s -> %s =/= 0 )' % (A2, C2))
    kc = st(w, A2, [c2cl(w, A2), vc2], 'mulcld', '%s e. CC' % K); kne = st(w, A2, [c2cl(w, A2), vc2, c2ne, vne], 'mulne0d', '%s =/= 0' % K)
    EX = EAT('V', 'x'); MAPX = '( x e. RR |-> %s )' % EX
    Ats = '( %s /\\ x e. RR )' % A2
    tcs = st(w, Ats, [w.s([], 'simpr', '( %s -> x e. RR )' % Ats)], 'recnd', 'x e. CC')
    evs = ap(w, Ats, 'eatcl', [lift(w, vc2, Ats), tcs], '%s e. CC' % EX)
    FM = '( x e. RR |-> ( %s / %s ) )' % (EX, K)
    fcl = st(w, Ats, [evs, lift(w, kc, Ats), lift(w, kne, Ats)], 'divcld', '( %s / %s ) e. CC' % (EX, K))
    ff = st(w, A2, [fcl], 'fmptd', '%s : RR --> CC' % FM)
    dG = ap(w, A2, 'eatdv', [vc2], '( RR _D %s ) = ( x e. RR |-> ( %s x. %s ) )' % (MAPX, K, EX))
    kev = st(w, Ats, [lift(w, kc, Ats), evs], 'mulcld', '( %s x. %s ) e. CC' % (K, EX))
    dF = st(w, A2, [a1(w, A2, 'reelprrecn', 'RR e. { RR , CC }'), evs, kev, dG, kc, kne], 'dvmptdivc',
            '( RR _D %s ) = ( x e. RR |-> ( ( %s x. %s ) / %s ) )' % (FM, K, EX, K))
    dF2 = st(w, A2, [st(w, Ats, [evs, lift(w, kc, Ats), lift(w, kne, Ats)], 'divcan3d', '( ( %s x. %s ) / %s ) = %s' % (K, EX, K, EX))], 'mpteq2dva',
             '( x e. RR |-> ( ( %s x. %s ) / %s ) ) = %s' % (K, EX, K, MAPX))
    dFG = eqt(w, A2, dF, dF2)
    gcn = ap(w, A2, 'eatcn', [vc2], '%s e. %s' % (MAPX, CNR))
    ftc = ap(w, A2, 'lsftc', [J(w, A2, J(w, A2, L2(cr), L2(c1r), L2(cle)), J(w, A2, ff, dFG, gcn))],
             '%s = ( ( %s ` ( C + 1 ) ) - ( %s ` C ) )' % (ITG(O, '( %s ` t )' % MAPX), FM, FM))
    Ato = '( %s /\\ t e. %s )' % (A2, O)
    tro = ap(w, Ato, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Ato, O))], 't e. RR')
    evo = ap(w, Ato, 'eatcl', [lift(w, vc2, Ato), st(w, Ato, [tro], 'recnd', 't e. CC')], '%s e. CC' % EV)
    gv = fvmd(w, Ato, 'x', 'RR', EX, 't', tro, evo)
    itq = st(w, A2, [gv], 'itgeq2dv', '%s = %s' % (ITG(O, '( %s ` t )' % MAPX), IT))
    c1c = st(w, A2, [L2(c1r)], 'recnd', '( C + 1 ) e. CC'); ccc = st(w, A2, [L2(cr)], 'recnd', 'C e. CC')
    e1c = ap(w, A2, 'eatcl', [vc2, c1c], '%s e. CC' % EAT('V', '( C + 1 )')); e0c = ap(w, A2, 'eatcl', [vc2, ccc], '%s e. CC' % EAT('V', 'C'))
    fv1 = fvmd(w, A2, 'x', 'RR', '( %s / %s )' % (EX, K), '( C + 1 )', L2(c1r), st(w, A2, [e1c, kc, kne], 'divcld', '( %s / %s ) e. CC' % (EAT('V', '( C + 1 )'), K)))
    fv0 = fvmd(w, A2, 'x', 'RR', '( %s / %s )' % (EX, K), 'C', L2(cr), st(w, A2, [e0c, kc, kne], 'divcld', '( %s / %s ) e. CC' % (EAT('V', 'C'), K)))
    per = ap(w, A2, 'eatper', [L2(vz), ccc], '%s = %s' % (EAT('V', '( C + 1 )'), EAT('V', 'C')))
    fv1b = eqt(w, A2, fv1, st(w, A2, [per], 'oveq1d', '( %s / %s ) = ( %s / %s )' % (EAT('V', '( C + 1 )'), K, EAT('V', 'C'), K)))
    df = eqt(w, A2, st(w, A2, [fv1b, fv0], 'oveq12d', '( ( %s ` ( C + 1 ) ) - ( %s ` C ) ) = ( ( %s / %s ) - ( %s / %s ) )' % (FM, FM, EAT('V', 'C'), K, EAT('V', 'C'), K)),
             st(w, A2, [st(w, A2, [e0c, kc, kne], 'divcld', '( %s / %s ) e. CC' % (EAT('V', 'C'), K))], 'subidd', '( ( %s / %s ) - ( %s / %s ) ) = 0' % (EAT('V', 'C'), K, EAT('V', 'C'), K)))
    case2 = eqc(w, A2, eqt(w, A2, eqt(w, A2, eqc(w, A2, itq), ftc), df))
    w.qed([eqc(w, A0, w.s([case1, case2], 'ifeqda', '( %s -> if ( V = 0 , 1 , 0 ) = %s )' % (A0, IT)))], 'id', STATEMENTS['eatitg']) if False else None
    ie = w.s([case1, case2], 'ifeqda', '( %s -> if ( V = 0 , 1 , 0 ) = %s )' % (A0, IT))
    eqc(w, A0, ie); qedlast(w); go(w)
