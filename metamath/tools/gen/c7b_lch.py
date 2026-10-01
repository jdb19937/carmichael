"""C7b section 3: the chi Lambda instance (lchvmval ... lchrconv, lvmbnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
lin.FASTPATH = True


def val(w, ante, body, k, mem, exs=None, x='n'):
    return _cg.mptval(w, ante, x, 'NN', body, k, mem, exs=exs, gen=w.g)


def ex_(w, ante, E, cc):
    return w.s([cc], 'elexd', '( %s -> %s e. _V )' % (ante, E))


def chl(w, ante, K, nxk):
    """( ante -> chi(K) e. CC ), ( ante -> ( Lam ` K ) e. RR ), ( ante -> 0 <_ ( Lam ` K ) ) from nxk: ( ante -> ( NX /\\ K e. NN ) )"""
    cc = w.s([nxk, w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (ante, CHV(K)))
    kn = w.s([nxk, w.inst('simpr')], 'syl', '( %s -> %s e. NN )' % (ante, K))
    lr = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` %s ) e. RR )' % (ante, K))
    l0 = w.s([kn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` %s ) )' % (ante, K))
    return cc, lr, l0, kn


def absvm(w, ante, K, nxk):
    """( ante -> ( abs ` ( chi(K) x. ( Lam ` K ) ) ) <_ ( Lam ` K ) )"""
    cc, lr, l0, kn = chl(w, ante, K, nxk)
    CL = '( %s x. ( Lam ` %s ) )' % (CHV(K), K)
    lc = w.s([lr], 'recnd', '( %s -> ( Lam ` %s ) e. CC )' % (ante, K))
    m = w.s([cc, lc], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( Lam ` %s ) ) ) )' % (ante, CL, CHV(K), K))
    ai = w.s([lr, l0], 'absidd', '( %s -> ( abs ` ( Lam ` %s ) ) = ( Lam ` %s ) )' % (ante, K, K))
    m2 = w.s([m, w.s([ai], 'oveq2d', '( %s -> ( ( abs ` %s ) x. ( abs ` ( Lam ` %s ) ) ) = ( ( abs ` %s ) x. ( Lam ` %s ) ) )' % (ante, CHV(K), K, CHV(K), K))],
             'eqtrd', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( Lam ` %s ) ) )' % (ante, CL, CHV(K), K))
    ab = w.s([nxk, w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (ante, CHV(K)))
    le = w.s([w.s([cc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ante, CHV(K))), w.s([], '1red', '( %s -> 1 e. RR )' % ante), lr, l0, ab], 'lemul1ad',
             '( %s -> ( ( abs ` %s ) x. ( Lam ` %s ) ) <_ ( 1 x. ( Lam ` %s ) ) )' % (ante, CHV(K), K, K))
    le2 = w.s([le, w.s([lc], 'mullidd', '( %s -> ( 1 x. ( Lam ` %s ) ) = ( Lam ` %s ) )' % (ante, K, K))], 'breqtrd',
              '( %s -> ( ( abs ` %s ) x. ( Lam ` %s ) ) <_ ( Lam ` %s ) )' % (ante, CHV(K), K, K))
    return w.s([m2, le2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( Lam ` %s ) )' % (ante, CL, K))


if __name__ == '__main__' and (not only or 'lchvmval' in only):
    w = W('lchvmval', 'The value of the coefficient mapping ` chi Lam ` .')
    ph = 'K e. NN'
    st, v = _cg.mptval(w, ph, 'q', 'NN', '( %s x. ( Lam ` q ) )' % CHV('q'), 'K', w.s([], 'id', '( K e. NN -> K e. NN )'), gen=w.g, name='qed')
    run7b(w)

if __name__ == '__main__' and (not only or 'lchvmf' in only):
    w = W('lchvmf', 'The coefficient mapping ` chi Lam ` is a complex sequence.')
    Aq = '( %s /\\ q e. NN )' % NX
    cc, lr, l0, kn = chl(w, Aq, 'q', w.s([], 'id', '( %s -> %s )' % (Aq, Aq)))
    b = w.s([cc, w.s([lr], 'recnd', '( %s -> ( Lam ` q ) e. CC )' % Aq)], 'mulcld', '( %s -> ( %s x. ( Lam ` q ) ) e. CC )' % (Aq, CHV('q')))
    w.qed([b, w.s([], 'eqid', '%s = %s' % (AXL, AXL))], 'fmptd', '( %s -> %s : NN --> CC )' % (NX, AXL))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchvmtm' in only):
    w = W('lchvmtm', 'The modulus of a term of the ` chi Lam ` series is at most the real von Mangoldt term at ` Re Z ` .')
    A0 = '( %s /\\ ( K e. NN /\\ Z e. CC ) )' % NX
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    kn = w.s([], 'simprl', '( %s -> K e. NN )' % A0)
    zc = w.s([], 'simprr', '( %s -> Z e. CC )' % A0)
    nxk = w.s([nx, kn], 'jca', '( %s -> ( %s /\\ K e. NN ) )' % (A0, NX))
    av = absvm(w, A0, 'K', nxk)
    cc, lr, l0, _ = chl(w, A0, 'K', nxk)
    CL = '( %s x. ( Lam ` K ) )' % CHV('K')
    clc = w.s([cc, w.s([lr], 'recnd', '( %s -> ( Lam ` K ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CL))
    pc = cxpz(w, A0, 'K', kn, zc)
    m = w.s([clc, pc], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( K ^c -u Z ) ) ) )' % (A0, VMT('K'), CL))
    ca = w.s([kn, zc, w.inst('cxpnnabs')], 'syl2anc', '( %s -> ( abs ` ( K ^c -u Z ) ) = ( K ^c -u %s ) )' % (A0, RZ))
    m2 = w.s([m, w.s([ca], 'oveq2d', '( %s -> ( ( abs ` %s ) x. ( abs ` ( K ^c -u Z ) ) ) = ( ( abs ` %s ) x. ( K ^c -u %s ) ) )' % (A0, CL, CL, RZ))],
             'eqtrd', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( K ^c -u %s ) ) )' % (A0, VMT('K'), CL, RZ))
    pr = w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0), w.s([w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))],
             'rpcxpcld', '( %s -> ( K ^c -u %s ) e. RR+ )' % (A0, RZ))
    le = w.s([w.s([clc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, CL)), lr, w.s([pr], 'rpred', '( %s -> ( K ^c -u %s ) e. RR )' % (A0, RZ)),
              w.s([pr], 'rpge0d', '( %s -> 0 <_ ( K ^c -u %s ) )' % (A0, RZ)), av], 'lemul1ad',
             '( %s -> ( ( abs ` %s ) x. ( K ^c -u %s ) ) <_ %s )' % (A0, CL, RZ, RVT('K', RZ)))
    w.qed([m2, le], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, VMT('K'), RVT('K', RZ)))
    run7b(w)


if __name__ == '__main__' and (not only or 'lchvmlav' in only):
    w = W('lchvmlav', 'The coefficients ` chi Lam ` satisfy the log-average bound of ~ dconvlim with ` K = log 4 + 4 ` (from ~ mertens1le ).')
    Ay = '( %s /\\ y e. RR )' % NX
    A1 = '( %s /\\ 1 <_ y )' % Ay
    RG = '( 1 ... ( |_ ` y ) )'
    Ad = '( %s /\\ d e. %s )' % (A1, RG)
    dn = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, RG)), w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % Ad)
    nxd = w.s([w.s([], 'simplll', '( %s -> %s )' % (Ad, NX)), dn], 'jca', '( %s -> ( %s /\\ d e. NN ) )' % (Ad, NX))
    av = absvm(w, Ad, 'd', nxd)
    cc, lr, l0, _ = chl(w, Ad, 'd', nxd)
    vv = w.s([dn, w.inst('lchvmval')], 'syl', '( %s -> ( %s ` d ) = ( %s x. ( Lam ` d ) ) )' % (Ad, AXL, CHV('d')))
    va = w.s([vv], 'fveq2d', '( %s -> ( abs ` ( %s ` d ) ) = ( abs ` ( %s x. ( Lam ` d ) ) ) )' % (Ad, AXL, CHV('d')))
    ab = w.s([va, av], 'eqbrtrd', '( %s -> ( abs ` ( %s ` d ) ) <_ ( Lam ` d ) )' % (Ad, AXL))
    drp = w.s([dn], 'nnrpd', '( %s -> d e. RR+ )' % Ad)
    AA = '( abs ` ( %s ` d ) )' % AXL
    aar = w.s([w.s([w.s([w.s([], 'simplll', '( %s -> %s )' % (Ad, NX)), w.inst('lchvmf')], 'syl', '( %s -> %s : NN --> CC )' % (Ad, AXL)), dn], 'ffvelcdmd',
                   '( %s -> ( %s ` d ) e. CC )' % (Ad, AXL))], 'abscld', '( %s -> %s e. RR )' % (Ad, AA))
    td = w.s([aar, lr, drp, ab], 'lediv1dd', '( %s -> ( %s / d ) <_ ( ( Lam ` d ) / d ) )' % (Ad, AA))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A1, RG))
    s1 = w.s([fin, w.s([aar, drp], 'rerpdivcld', '( %s -> ( %s / d ) e. RR )' % (Ad, AA)), w.s([lr, drp], 'rerpdivcld', '( %s -> ( ( Lam ` d ) / d ) e. RR )' % Ad), td],
             'fsumle', '( %s -> sum_ d e. %s ( %s / d ) <_ sum_ d e. %s ( ( Lam ` d ) / d ) )' % (A1, RG, AA, RG))
    yr = w.s([], 'simplr', '( %s -> y e. RR )' % A1)
    y1 = w.s([], 'simpr', '( %s -> 1 <_ y )' % A1)
    mt = w.s([yr, y1, w.inst('mertens1le')], 'syl2anc', '( %s -> sum_ d e. %s ( ( Lam ` d ) / d ) <_ ( ( log ` y ) + %s ) )' % (A1, RG, K4))
    SA = 'sum_ d e. %s ( %s / d )' % (RG, AA)
    SL = 'sum_ d e. %s ( ( Lam ` d ) / d )' % RG
    ypos = lin.linarith(w, A1, [y1], '0 < y', leaves={'y': yr})
    yrp = w.s([yr, ypos], 'elrpd', '( %s -> y e. RR+ )' % A1)
    c = cl.Closure(w, A1, {'y': [yr, ('RR+', yrp)]})
    RHS = '( ( log ` y ) + %s )' % K4
    s2 = w.s([w.s([fin, w.s([aar, drp], 'rerpdivcld', '( %s -> ( %s / d ) e. RR )' % (Ad, AA))], 'fsumrecl', '( %s -> %s e. RR )' % (A1, SA)),
              w.s([fin, w.s([lr, drp], 'rerpdivcld', '( %s -> ( ( Lam ` d ) / d ) e. RR )' % Ad)], 'fsumrecl', '( %s -> %s e. RR )' % (A1, SL)),
              c.mem(RHS, 'RR'), s1, mt], 'letrd', '( %s -> %s <_ %s )' % (A1, SA, RHS))
    im = w.s([s2], 'ex', '( %s -> ( 1 <_ y -> %s <_ %s ) )' % (Ay, SA, RHS))
    ral = w.s([im], 'ralrimiva', '( %s -> A. y e. RR ( 1 <_ y -> %s <_ %s ) )' % (NX, SA, RHS))
    c0 = cl.Closure(w, NX, {})
    w.qed([w.s([], 'lchvmf', '( %s -> %s : NN --> CC )' % (NX, AXL)), c0.mem(K4, 'RR'), ral], '3jca', '( %s -> %s )' % (NX, LAV(AXL, K4)))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchvmcv' in only):
    w = W('lchvmcv', 'The Dirichlet convolution of ` chi Lam ` and ` chi ` is ` chi log ` (from ~ vmachsum ).')
    A0 = '( %s /\\ K e. NN )' % NX
    DV = '{ x e. NN | x || K }'
    Ad = '( %s /\\ d e. %s )' % (A0, DV)
    dd = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, DV))
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DV)], 'a1i', '( %s -> %s C_ NN )' % (Ad, DV))
    dn = w.s([ss, dd], 'sseldd', '( %s -> d e. NN )' % Ad)
    kd = w.s([w.s([], 'simpr', '( %s -> K e. NN )' % A0)], 'adantr', '( %s -> K e. NN )' % Ad)
    qn = w.s([ss, w.s([kd, dd, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( K / d ) e. %s )' % (Ad, DV))], 'sseldd', '( %s -> ( K / d ) e. NN )' % Ad)
    v1 = w.s([dn, w.inst('lchvmval')], 'syl', '( %s -> ( %s ` d ) = ( %s x. ( Lam ` d ) ) )' % (Ad, AXL, CHV('d')))
    nxq = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, NX))], 'adantr', '( %s -> %s )' % (Ad, NX)), qn], 'jca', '( %s -> ( %s /\\ ( K / d ) e. NN ) )' % (Ad, NX))
    v2 = w.s([nxq, w.inst('lchrval')], 'syl', '( %s -> ( %s ` ( K / d ) ) = %s )' % (Ad, AX, CHV('( K / d )')))
    t = w.s([v1, v2], 'oveq12d', '( %s -> ( ( %s ` d ) x. ( %s ` ( K / d ) ) ) = ( ( %s x. ( Lam ` d ) ) x. %s ) )' % (Ad, AXL, AX, CHV('d'), CHV('( K / d )')))
    s = w.s([t], 'sumeq2dv', '( %s -> %s = sum_ d e. %s ( ( %s x. ( Lam ` d ) ) x. %s ) )' % (A0, CV('K', AXL, AX), DV, CHV('d'), CHV('( K / d )')))
    vs = w.s([], 'vmachsum', '( %s -> sum_ d e. %s ( ( %s x. ( Lam ` d ) ) x. %s ) = ( %s x. ( log ` K ) ) )' % (A0, DV, CHV('d'), CHV('( K / d )'), CHV('K')))
    w.qed([s, vs], 'eqtrd', '( %s -> %s = ( %s x. ( log ` K ) ) )' % (A0, CV('K', AXL, AX), CHV('K')))
    run7b(w)

NXZ = '( %s /\\ %s )' % (NX, ZP1)


def nxzctx(w, A0):
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    zp = w.s([], 'simpr', '( %s -> %s )' % (A0, ZP1))
    return nx, zp


def vmtcl(w, Ak, K, nx, kn, zc):
    """( Ak -> VMT(K) e. CC )"""
    nxk = w.s([nx, kn], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (Ak, NX, K))
    cc, lr, l0, _ = chl(w, Ak, K, nxk)
    CL = '( %s x. ( Lam ` %s ) )' % (CHV(K), K)
    clc = w.s([cc, w.s([lr], 'recnd', '( %s -> ( Lam ` %s ) e. CC )' % (Ak, K))], 'mulcld', '( %s -> %s e. CC )' % (Ak, CL))
    return w.s([clc, cxpz(w, Ak, K, kn, zc)], 'mulcld', '( %s -> %s e. CC )' % (Ak, VMT(K)))


if __name__ == '__main__' and (not only or 'lchvmacvg' in only):
    w = W('lchvmacvg', 'The ` chi Lam ` Dirichlet series converges absolutely on ` Re Z > 1 ` .')
    A0 = NXZ
    nx, zp = nxzctx(w, A0)
    z = zctx(w, A0, zp)
    F = '( n e. NN |-> %s )' % RVT('n', RZ)
    G = '( n e. NN |-> ( abs ` %s ) )' % VMT('n')
    fcv = w.s([w.s([z['rz'], z['z1']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)), w.inst('vmsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, F))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX))
    zck = w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % Ak)
    vc = vmtcl(w, Ak, 'k', nxk, kn, zck)
    avr = w.s([vc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, VMT('k')))
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    pr = w.s([krp, w.s([w.s([z['rz']], 'adantr', '( %s -> %s e. RR )' % (Ak, RZ))], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, RZ))], 'rpcxpcld',
             '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, RZ))
    rvr = w.s([w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % Ak), w.s([pr], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))], 'remulcld',
              '( %s -> %s e. RR )' % (Ak, RVT('k', RZ)))
    vf, _ = val(w, Ak, RVT('n', RZ), 'k', kn, ex_(w, Ak, RVT('k', RZ), w.s([rvr], 'recnd', '( %s -> %s e. CC )' % (Ak, RVT('k', RZ)))))
    vg, _ = val(w, Ak, '( abs ` %s )' % VMT('n'), 'k', kn, ex_(w, Ak, '( abs ` %s )' % VMT('k'), w.s([avr], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, VMT('k')))))
    f3 = w.s([vf, rvr], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, F))
    g4 = w.s([vg, avr], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, G))
    g0 = w.s([w.s([vc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Ak, VMT('k'))), vg], 'breqtrrd', '( %s -> 0 <_ ( %s ` k ) )' % (Ak, G))
    tm = w.s([w.s([nxk, w.s([kn, zck], 'jca', '( %s -> ( k e. NN /\\ Z e. CC ) )' % Ak)], 'jca', '( %s -> ( %s /\\ ( k e. NN /\\ Z e. CC ) ) )' % (Ak, NX)),
              w.inst('lchvmtm')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (Ak, VMT('k'), RVT('k', RZ)))
    le = w.s([w.s([vg, tm], 'eqbrtrd', '( %s -> ( %s ` k ) <_ %s )' % (Ak, G, RVT('k', RZ))), vf], 'breqtrrd', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Ak, G, F))
    Bk = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A0
    kn2 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Bk), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrrdi', '( %s -> k e. NN )' % Bk)
    jb = w.s([w.s([], 'simpl', '( %s -> %s )' % (Bk, A0)), kn2], 'jca', '( %s -> %s )' % (Bk, Ak))
    w.qed([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0), f3, g4, fcv,
           w.s([jb, g0], 'syl', '( %s -> 0 <_ ( %s ` k ) )' % (Bk, G)), w.s([jb, le], 'syl', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Bk, G, F))],
          'cvgcmp', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, G))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchvmcvg' in only):
    w = W('lchvmcvg', 'The ` chi Lam ` Dirichlet series converges on ` Re Z > 1 ` .')
    A0 = NXZ
    nx, zp = nxzctx(w, A0)
    z = zctx(w, A0, zp)
    F = '( n e. NN |-> ( abs ` %s ) )' % VMT('n')
    G = '( n e. NN |-> %s )' % VMT('n')
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    vc = vmtcl(w, Ak, 'k', w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)), kn, w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % Ak))
    avc = w.s([w.s([vc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, VMT('k')))], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, VMT('k')))
    vf, _ = val(w, Ak, '( abs ` %s )' % VMT('n'), 'k', kn, ex_(w, Ak, '( abs ` %s )' % VMT('k'), avc))
    vg, _ = val(w, Ak, VMT('n'), 'k', kn, ex_(w, Ak, VMT('k'), vc))
    fg = w.s([vf, w.s([vg], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, G, VMT('k')))], 'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, F, G))
    gc = w.s([vg, vc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G))
    w.qed([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0), fg, gc, w.s([], 'lchvmacvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, F))],
          'abscvgcvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, G))
    run7b(w)


def dchinst(w, A0, A, B, Kc, Cc, lav, cfb, zp, mapeq, cvg2):
    """( A0 -> DCH[A,B,K,C] ) from lav, cfb, zp and cvg2: ( A0 -> seq 1 ( + , M2 ) e. dom ~~> ),
    mapeq: ( A0 -> MAP(A) = M2 )"""
    se = w.s([mapeq], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (A0, MAP(A), formula_of_rhs(w, mapeq)))
    bi = w.s([se], 'eleq1d', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A0, MAP(A), formula_of_rhs(w, mapeq)))
    cv = w.s([cvg2, bi], 'mpbird', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAP(A)))
    D = '( ( %s /\\ %s ) /\\ ( %s /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (LAV(A, Kc), CFBX(B, Cc), ZP1, MAP(A))
    return w.s([w.s([lav, cfb], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, LAV(A, Kc), CFBX(B, Cc))),
                w.s([zp, cv], 'jca', '( %s -> ( %s /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (A0, ZP1, MAP(A)))], 'jca', '( %s -> %s )' % (A0, D)), D


def formula_of_rhs(w, st):
    f = formula_of(w, st)
    # ( ante -> L = R ): take R
    from congr import parse_wff
    n = parse_wff(f)
    return n.kids[1].kids[1].text()


def conv_results(w, A0, A, B, Kc, Cc, dch, D):
    """apply dconvlim; returns (dom-step, sum-step) in the raw form"""
    r = w.s([dch, w.inst('dconvlim')], 'syl', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ %s = ( %s x. %s ) ) )' % (
        A0, CMAP(A=A, B=B), CSER(A=A, B=B), SER(A), SER(B)))
    d = w.s([r], 'simpld', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, CMAP(A=A, B=B)))
    s = w.s([r], 'simprd', '( %s -> %s = ( %s x. %s ) )' % (A0, CSER(A=A, B=B), SER(A), SER(B)))
    return d, s


if __name__ == '__main__' and (not only or 'lchrconvlem' in only):
    w = W('lchrconvlem', 'The ` chi log ` series converges and ` L ( chi Lam ) L ( chi ) = L ( chi log ) ` on ` Re Z > 1 ` '
          '(Mathlib ` LSeries_twist_vonMangoldt_eq ` before the sign), the instance of ~ dconvlim at ` A = chi Lam ` , ` B = chi ` .')
    A0 = NXZ
    nx, zp = nxzctx(w, A0)
    z = zctx(w, A0, zp)
    lav = w.s([nx, w.inst('lchvmlav')], 'syl', '( %s -> %s )' % (A0, LAV(AXL, K4)))
    cfb = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AX, '1')))
    An = '( %s /\\ n e. NN )' % A0
    nn = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    vv = w.s([nn, w.inst('lchvmval')], 'syl', '( %s -> ( %s ` n ) = ( %s x. ( Lam ` n ) ) )' % (An, AXL, CHV('n')))
    meq = w.s([w.s([vv], 'oveq1d', '( %s -> %s = %s )' % (An, TRM(AXL, 'n'), VMT('n')))], 'mpteq2dva', '( %s -> %s = ( n e. NN |-> %s ) )' % (A0, MAP(AXL), VMT('n')))
    cvg = w.s([], 'lchvmcvg', '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A0, VMT('n')))
    dch, D = dchinst(w, A0, AXL, AX, K4, '1', lav, cfb, zp, meq, cvg)
    dm, sm = conv_results(w, A0, AXL, AX, K4, '1', dch, D)
    # rewriting to the chi forms
    nxn = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (An, NX)), nn], 'jca', '( %s -> ( %s /\\ n e. NN ) )' % (An, NX))
    cvn = w.s([nxn, w.inst('lchvmcv')], 'syl', '( %s -> %s = ( %s x. ( log ` n ) ) )' % (An, CV('n', AXL, AX), CHV('n')))
    ceq = w.s([w.s([cvn], 'oveq1d', '( %s -> %s = %s )' % (An, CTRM('n', A=AXL, B=AX), LGT('n')))], 'mpteq2dva', '( %s -> %s = ( n e. NN |-> %s ) )' % (A0, CMAP(A=AXL, B=AX), LGT('n')))
    d2 = w.s([dm, w.s([w.s([ceq], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , ( n e. NN |-> %s ) ) )' % (A0, CMAP(A=AXL, B=AX), LGT('n')))], 'eleq1d',
                     '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> ) )' % (A0, CMAP(A=AXL, B=AX), LGT('n')))], 'mpbid',
             '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A0, LGT('n')))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)), kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX))
    cvk = w.s([nxk, w.inst('lchvmcv')], 'syl', '( %s -> %s = ( %s x. ( log ` k ) ) )' % (Ak, CV('k', AXL, AX), CHV('k')))
    s1 = w.s([w.s([cvk], 'oveq1d', '( %s -> %s = %s )' % (Ak, CTRM('k', A=AXL, B=AX), LGT('k')))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (A0, CSER(A=AXL, B=AX), LGT('k')))
    vk = w.s([kn, w.inst('lchvmval')], 'syl', '( %s -> ( %s ` k ) = ( %s x. ( Lam ` k ) ) )' % (Ak, AXL, CHV('k')))
    s2 = w.s([w.s([vk], 'oveq1d', '( %s -> %s = %s )' % (Ak, TRM(AXL, 'k'), VMT('k')))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (A0, SER(AXL), VMT('k')))
    ck = w.s([nxk, w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, AX, CHV('k')))
    s3 = w.s([w.s([ck], 'oveq1d', '( %s -> %s = %s )' % (Ak, TRM(AX, 'k'), CHT('k')))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (A0, SER(AX), CHT('k')))
    s23 = w.s([s2, s3], 'oveq12d', '( %s -> ( %s x. %s ) = ( sum_ k e. NN %s x. sum_ k e. NN %s ) )' % (A0, SER(AXL), SER(AX), VMT('k'), CHT('k')))
    fin = w.s([w.s([s1, sm], 'eqtr3d', '( %s -> sum_ k e. NN %s = ( %s x. %s ) )' % (A0, LGT('k'), SER(AXL), SER(AX))), s23], 'eqtrd',
              '( %s -> sum_ k e. NN %s = ( sum_ k e. NN %s x. sum_ k e. NN %s ) )' % (A0, LGT('k'), VMT('k'), CHT('k')))
    w.qed([d2, w.s([fin], 'eqcomd', '( %s -> ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s )' % (A0, VMT('k'), CHT('k'), LGT('k')))], 'jca',
          '( %s -> ( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> /\\ ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s ) )' % (A0, LGT('n'), VMT('k'), CHT('k'), LGT('k')))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchlgcvg' in only):
    w = W('lchlgcvg', 'The ` chi log ` Dirichlet series converges on ` Re Z > 1 ` .')
    r = w.s([], 'lchrconvlem', '( %s -> ( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> /\\ ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s ) )' % (NXZ, LGT('n'), VMT('k'), CHT('k'), LGT('k')))
    w.qed([r], 'simpld', '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (NXZ, LGT('n')))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchrconv' in only):
    w = W('lchrconv', '` L ( chi Lam ) L ( chi ) = L ( chi log ) ` on ` Re Z > 1 ` (Mathlib ` LSeries_twist_vonMangoldt_eq ` up to the sign of the derivative).')
    r = w.s([], 'lchrconvlem', '( %s -> ( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> /\\ ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s ) )' % (NXZ, LGT('n'), VMT('k'), CHT('k'), LGT('k')))
    w.qed([r], 'simprd', '( %s -> ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s )' % (NXZ, VMT('k'), CHT('k'), LGT('k')))
    run7b(w)


if __name__ == '__main__' and (not only or 'lvmbnd' in only):
    w = W('lvmbnd', 'Lean ` norm_logDeriv_LFunction_le ` \'s bound: ` abs ` L ( chi Lam ) <_ 6 / ( Re Z - 1 ) ^ 2 ` for ` 1 < Re Z <_ 2 ` '
          '(from ~ vmbnd at ` T = Re Z ` ).')
    A0 = '( %s /\\ ( Z e. CC /\\ ( 1 < %s /\\ %s <_ 2 ) ) )' % (NX, RZ, RZ)
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
    zz = w.s([], 'simprr', '( %s -> ( 1 < %s /\\ %s <_ 2 ) )' % (A0, RZ, RZ))
    z1 = w.s([zz], 'simpld', '( %s -> 1 < %s )' % (A0, RZ))
    z2 = w.s([zz], 'simprd', '( %s -> %s <_ 2 )' % (A0, RZ))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    nxz = w.s([nx, w.s([zc, z1], 'jca', '( %s -> %s )' % (A0, ZP1))], 'jca', '( %s -> %s )' % (A0, NXZ))
    F = '( n e. NN |-> %s )' % VMT('n')
    G = '( n e. NN |-> ( abs ` %s ) )' % VMT('n')
    H = '( n e. NN |-> %s )' % RVT('n', RZ)
    fcv = w.s([nxz, w.inst('lchvmcvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, F))
    gcv = w.s([nxz, w.inst('lchvmacvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, G))
    hcv = w.s([w.s([rz, z1], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)), w.inst('vmsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, H))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX))
    zck = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)
    vc = vmtcl(w, Ak, 'k', nxk, kn, zck)
    avr = w.s([vc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, VMT('k')))
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    pr = w.s([krp, w.s([w.s([rz], 'adantr', '( %s -> %s e. RR )' % (Ak, RZ))], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, RZ))], 'rpcxpcld',
             '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, RZ))
    rvr = w.s([w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % Ak), w.s([pr], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))], 'remulcld',
              '( %s -> %s e. RR )' % (Ak, RVT('k', RZ)))
    vf, _ = val(w, Ak, VMT('n'), 'k', kn, ex_(w, Ak, VMT('k'), vc))
    vg, _ = val(w, Ak, '( abs ` %s )' % VMT('n'), 'k', kn, ex_(w, Ak, '( abs ` %s )' % VMT('k'), w.s([avr], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, VMT('k')))))
    vh, _ = val(w, Ak, RVT('n', RZ), 'k', kn, ex_(w, Ak, RVT('k', RZ), w.s([rvr], 'recnd', '( %s -> %s e. CC )' % (Ak, RVT('k', RZ)))))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0)
    SV = 'sum_ k e. NN %s' % VMT('k')
    SA = 'sum_ k e. NN ( abs ` %s )' % VMT('k')
    SR = 'sum_ k e. NN %s' % RVT('k', RZ)
    lf = w.s([nnuz, one, vf, vc, fcv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, F, SV))
    lg = w.s([nnuz, one, vg, w.s([avr], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, VMT('k'))), gcv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, G, SA))
    fkc = w.s([vf, vc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F))
    gk = w.s([vg, w.s([vf], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, F, VMT('k')))], 'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, G, F))
    ia = w.s([nnuz, lf, lg, one, fkc, gk], 'iserabs', '( %s -> ( abs ` %s ) <_ %s )' % (A0, SV, SA))
    tm = w.s([w.s([nxk, w.s([kn, zck], 'jca', '( %s -> ( k e. NN /\\ Z e. CC ) )' % Ak)], 'jca', '( %s -> ( %s /\\ ( k e. NN /\\ Z e. CC ) ) )' % (Ak, NX)),
              w.inst('lchvmtm')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (Ak, VMT('k'), RVT('k', RZ)))
    il = w.s([nnuz, one, vg, avr, vh, rvr, tm, gcv, hcv], 'isumle', '( %s -> %s <_ %s )' % (A0, SA, SR))
    R = '( 6 / ( %s ^ 2 ) )' % E1
    vb = w.s([w.s([rz, z1, z2], '3jca', '( %s -> ( %s e. RR /\\ 1 < %s /\\ %s <_ 2 ) )' % (A0, RZ, RZ, RZ)), w.inst('vmbnd')], 'syl', '( %s -> %s <_ %s )' % (A0, SR, R))
    svc = w.s([nnuz, one, vf, vc, fcv], 'isumcl', '( %s -> %s e. CC )' % (A0, SV))
    sar = w.s([nnuz, one, vg, avr, gcv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SA))
    srr = w.s([nnuz, one, vh, rvr, hcv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SR))
    z = zctx(w, A0, w.s([zc, z1], 'jca', '( %s -> %s )' % (A0, ZP1)))
    e2p = w.s([z['e1rp'], w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A0)], 'rpexpcld', '( %s -> ( %s ^ 2 ) e. RR+ )' % (A0, E1))
    rr = w.s([w.s([w.s([], '6re', '6 e. RR')], 'a1i', '( %s -> 6 e. RR )' % A0), e2p], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, R))
    l1 = w.s([sar, srr, rr, il, vb], 'letrd', '( %s -> %s <_ %s )' % (A0, SA, R))
    w.qed([w.s([svc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, SV)), sar, rr, ia, l1], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, SV, R))
    run7b(w)
