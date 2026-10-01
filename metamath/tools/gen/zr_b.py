"""Sortie ZR: zrvmc (convergence of the von Mangoldt series), zr341t, zr341 (the 3-4-1 inequality)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift

CHN = '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` n ) )' % U1
VMF = lambda z: '( n e. NN |-> ( ( Lam ` n ) x. ( n ^c -u %s ) ) )' % z


def gen_vmc():
    w = W('zrvmc', 'Convergence of the von Mangoldt series ` sum Lam ( n ) n ^ -s ` on ` 1 < Re s ` ( ~ lchvmcvg at the character mod ` 1 ` , ~ zc1x1 ).')
    A0 = ante_of(S['zrvmc'])[0]
    c = Ctx(w, A0)
    zc = c.g('Z e. CC'); z1 = c.g('1 < ( Re ` Z )')
    nx = nx1(w, A0)
    B1 = '( ( %s x. ( Lam ` n ) ) x. ( n ^c -u Z ) )' % CHN
    M1 = '( n e. NN |-> %s )' % B1
    cv = c([c([nx, c([zc, z1], 'jca', '( Z e. CC /\\ 1 < ( Re ` Z ) )')], 'jca', '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % U1),
            w.inst('lchvmcvg')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % M1)
    An = '( %s /\\ n e. NN )' % A0
    cn = Ctx(w, An)
    nn_ = cn([], 'simpr', 'n e. NN')
    ub = cn([lift(w, nx, An)], 'simprd', '%s e. ( Base ` ( DChr ` 1 ) )' % U1)
    x1 = cn([ub, cn([nn_], 'nnzd', 'n e. ZZ'), w.inst('zc1x1')], 'syl2anc', '%s = 1' % CHN)
    lc = cn([cn([nn_, w.inst('vmacl')], 'syl', '( Lam ` n ) e. RR')], 'recnd', '( Lam ` n ) e. CC')
    e1 = cn([x1], 'oveq1d', '( %s x. ( Lam ` n ) ) = ( 1 x. ( Lam ` n ) )' % CHN)
    e2 = cn([e1, cn([lc], 'mullidd', '( 1 x. ( Lam ` n ) ) = ( Lam ` n )')], 'eqtrd', '( %s x. ( Lam ` n ) ) = ( Lam ` n )' % CHN)
    e3 = cn([e2], 'oveq1d', '%s = ( ( Lam ` n ) x. ( n ^c -u Z ) )' % B1)
    me = c([e3], 'mpteq2dva', '%s = %s' % (M1, VMF('Z')))
    se = c([me], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (M1, VMF('Z')))
    fin = c([cv, c([se], 'eleq1d', '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (M1, VMF('Z')))], 'mpbid', 'seq 1 ( + , %s ) e. dom ~~>' % VMF('Z'))
    w.qed([fin], 'idi', S['zrvmc'])
    return run8(w)


def gen_341t():
    w = W('zr341t', 'One term of the 3-4-1 inequality: ` 3 + 4 cos theta + cos 2 theta = 2 ( 1 + cos theta ) ^ 2 >_ 0 ` , written with ` u = K ^ -u ( i T ) ` , ` abs u = 1 ` .')
    A0 = ante_of(S['zr341t'])[0]
    c = Ctx(w, A0)
    kn = c.g('K e. NN'); xr = c.g('X e. RR'); tr = c.g('T e. RR')
    kc = c([kn], 'nncnd', 'K e. CC'); kp = c([kn], 'nnrpd', 'K e. RR+'); k0 = c([kn], 'nnne0d', 'K =/= 0')
    xc = c([xr], 'recnd', 'X e. CC'); tc = c([tr], 'recnd', 'T e. CC')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    IT = '( _i x. T )'
    itc = c([ic, tc], 'mulcld', '%s e. CC' % IT)
    nit = c([itc], 'negcld', '-u %s e. CC' % IT)
    nx = c([xc], 'negcld', '-u X e. CC')
    u = '( K ^c -u %s )' % IT
    uc = c([kc, nit], 'cxpcld', '%s e. CC' % u)
    q = '( K ^c -u X )'
    qr = c([c([kp, c([xr], 'renegcld', '-u X e. RR')], 'rpcxpcld', '%s e. RR+' % q)], 'rpred', '%s e. RR' % q)
    L = '( Lam ` K )'
    lr = c([kn, w.inst('vmacl')], 'syl', '%s e. RR' % L)
    l0 = c([kn, w.inst('vmage0')], 'syl', '0 <_ %s' % L)
    p_ = '( %s x. %s )' % (L, q)
    pr = c([lr, qr], 'remulcld', '%s e. RR' % p_)
    q0 = c([c([kp, c([xr], 'renegcld', '-u X e. RR')], 'rpcxpcld', '%s e. RR+' % q)], 'rpge0d', '0 <_ %s' % q)
    p0 = c([lr, qr, l0, q0], 'mulge0d', '0 <_ %s' % p_)
    pc = c([pr], 'recnd', '%s e. CC' % p_)
    cl = Closure(w, A0, {'X': ('CC', xc), 'T': ('CC', tc), '_i': ('CC', ic)})
    for a in ('X', 'T', '_i'):
        cl.atom(a)
    X1_, X2_ = '( X + ( _i x. T ) )', '( X + ( _i x. ( 2 x. T ) ) )'
    r1 = ringeq(w, A0, '-u %s' % X1_, '( -u X + -u %s )' % IT, cl)
    r2 = ringeq(w, A0, '-u %s' % X2_, '( -u X + ( -u %s + -u %s ) )' % (IT, IT), cl)
    k1 = c([c([r1], 'oveq2d', '( K ^c -u %s ) = ( K ^c ( -u X + -u %s ) )' % (X1_, IT)), c([kc, k0, nx, nit], 'cxpaddd', '( K ^c ( -u X + -u %s ) ) = ( %s x. %s )' % (IT, q, u))],
           'eqtrd', '( K ^c -u %s ) = ( %s x. %s )' % (X1_, q, u))
    uu = '( %s x. %s )' % (u, u)
    nn2 = c([nit, nit], 'addcld', '( -u %s + -u %s ) e. CC' % (IT, IT))
    k2a = c([kc, k0, nx, nn2], 'cxpaddd', '( K ^c ( -u X + ( -u %s + -u %s ) ) ) = ( %s x. ( K ^c ( -u %s + -u %s ) ) )' % (IT, IT, q, IT, IT))
    k2b = c([kc, k0, nit, nit], 'cxpaddd', '( K ^c ( -u %s + -u %s ) ) = %s' % (IT, IT, uu))
    k2 = c([c([c([r2], 'oveq2d', '( K ^c -u %s ) = ( K ^c ( -u X + ( -u %s + -u %s ) ) )' % (X2_, IT, IT)), k2a], 'eqtrd',
              '( K ^c -u %s ) = ( %s x. ( K ^c ( -u %s + -u %s ) ) )' % (X2_, q, IT, IT)), c([k2b], 'oveq2d', '( %s x. ( K ^c ( -u %s + -u %s ) ) ) = ( %s x. %s )' % (q, IT, IT, q, uu))],
           'eqtrd', '( K ^c -u %s ) = ( %s x. %s )' % (X2_, q, uu))
    lc = c([lr], 'recnd', '%s e. CC' % L); qc = c([qr], 'recnd', '%s e. CC' % q)
    # term values
    T0 = TK('K', 'X'); T1 = TK('K', X1_); T2 = TK('K', X2_)
    t0 = c([pr], 'rered', '( Re ` %s ) = %s' % (p_, p_))
    a1 = c([c([k1], 'oveq2d', '( %s x. ( K ^c -u %s ) ) = ( %s x. ( %s x. %s ) )' % (L, X1_, L, q, u)), c([lc, qc, uc], 'mulassd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (p_, u, L, q, u))],
           'eqtr4d', '( %s x. ( K ^c -u %s ) ) = ( %s x. %s )' % (L, X1_, p_, u))
    t1 = c([c([a1], 'fveq2d', '%s = ( Re ` ( %s x. %s ) )' % (T1, p_, u)), c([pr, uc], 'remul2d', '( Re ` ( %s x. %s ) ) = ( %s x. ( Re ` %s ) )' % (p_, u, p_, u))],
           'eqtrd', '%s = ( %s x. ( Re ` %s ) )' % (T1, p_, u))
    uuc = c([uc, uc], 'mulcld', '%s e. CC' % uu)
    a2 = c([c([k2], 'oveq2d', '( %s x. ( K ^c -u %s ) ) = ( %s x. ( %s x. %s ) )' % (L, X2_, L, q, uu)), c([lc, qc, uuc], 'mulassd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (p_, uu, L, q, uu))],
           'eqtr4d', '( %s x. ( K ^c -u %s ) ) = ( %s x. %s )' % (L, X2_, p_, uu))
    RU, IU = '( Re ` %s )' % u, '( Im ` %s )' % u
    t2a = c([c([a2], 'fveq2d', '%s = ( Re ` ( %s x. %s ) )' % (T2, p_, uu)), c([pr, uuc], 'remul2d', '( Re ` ( %s x. %s ) ) = ( %s x. ( Re ` %s ) )' % (p_, uu, p_, uu))],
            'eqtrd', '%s = ( %s x. ( Re ` %s ) )' % (T2, p_, uu))
    t2b = c([uc, uc], 'remuld', '( Re ` %s ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (uu, RU, RU, IU, IU))
    t2 = c([t2a, c([t2b], 'oveq2d', '( %s x. ( Re ` %s ) ) = ( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (p_, uu, p_, RU, RU, IU, IU))],
           'eqtrd', '%s = ( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (T2, p_, RU, RU, IU, IU))
    # abs u = 1
    ab = c([kp, nit, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( K ^c ( Re ` -u %s ) )' % (u, IT))
    z0 = c([c([ic, tc], 'mulcld', '%s e. CC' % IT)], 'addlidd', '( 0 + %s ) = %s' % (IT, IT))
    cr = c([c([], '0red', '0 e. RR'), tr, w.inst('crre')], 'syl2anc', '( Re ` ( 0 + %s ) ) = 0' % IT)
    ri = c([c([z0], 'fveq2d', '( Re ` ( 0 + %s ) ) = ( Re ` %s )' % (IT, IT)), cr], 'eqtr3d', '( Re ` %s ) = 0' % IT)
    rn = c([c([itc], 'renegd', '( Re ` -u %s ) = -u ( Re ` %s )' % (IT, IT)), c([ri], 'negeqd', '-u ( Re ` %s ) = -u 0' % IT)], 'eqtrd', '( Re ` -u %s ) = -u 0' % IT)
    rn0 = c([rn, c.a1(w.s([], 'neg0', '-u 0 = 0'), '-u 0 = 0')], 'eqtrd', '( Re ` -u %s ) = 0' % IT)
    ab1 = c([ab, c([c([rn0], 'oveq2d', '( K ^c ( Re ` -u %s ) ) = ( K ^c 0 )' % IT), c([kc], 'cxp0d', '( K ^c 0 ) = 1')], 'eqtrd', '( K ^c ( Re ` -u %s ) ) = 1' % IT)],
            'eqtrd', '( abs ` %s ) = 1' % u)
    sq = c([c([uc], 'absvalsq2d', '( ( abs ` %s ) ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (u, RU, IU)), c([ab1], 'oveq1d', '( ( abs ` %s ) ^ 2 ) = ( 1 ^ 2 )' % u)],
           'eqtr3d', '( ( %s ^ 2 ) + ( %s ^ 2 ) ) = ( 1 ^ 2 )' % (RU, IU))
    rur = c([uc], 'recld', '%s e. RR' % RU); iur = c([uc], 'imcld', '%s e. RR' % IU)
    lvp = {RU: rur, IU: iur}
    ps = c([sq], 'oveq2d', '( %s x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) ) = ( %s x. ( 1 ^ 2 ) )' % (p_, RU, IU, p_))
    op = '( 1 + %s )' % RU
    opr = c([c([], '1red', '1 e. RR'), rur], 'readdcld', '%s e. RR' % op)
    g0 = c([pr, c([opr, opr], 'remulcld', '( %s x. %s ) e. RR' % (op, op)), p0, c([opr], 'msqge0d', '0 <_ ( %s x. %s )' % (op, op))], 'mulge0d', '0 <_ ( %s x. ( %s x. %s ) )' % (p_, op, op))
    lv = {p_: pr, RU: rur, IU: iur, T0: c([c([lc, qc], 'mulcld', '%s e. CC' % p_)], 'recld', '%s e. RR' % T0)}
    lv[T1] = c([c([lc, c([kc, c([c([xc, itc], 'addcld', '%s e. CC' % X1_)], 'negcld', '-u %s e. CC' % X1_)], 'cxpcld', '( K ^c -u %s ) e. CC' % X1_)], 'mulcld', '( %s x. ( K ^c -u %s ) ) e. CC' % (L, X1_))], 'recld', '%s e. RR' % T1)
    it2 = c([ic, c([c([], '2cnd', '2 e. CC'), tc], 'mulcld', '( 2 x. T ) e. CC')], 'mulcld', '( _i x. ( 2 x. T ) ) e. CC')
    lv[T2] = c([c([lc, c([kc, c([c([xc, it2], 'addcld', '%s e. CC' % X2_)], 'negcld', '-u %s e. CC' % X2_)], 'cxpcld', '( K ^c -u %s ) e. CC' % X2_)], 'mulcld', '( %s x. ( K ^c -u %s ) ) e. CC' % (L, X2_))], 'recld', '%s e. RR' % T2)
    fin = lin8(w, A0, [t0, t1, t2, ps, g0], ante_of(S['zr341t'])[1], lv, products=True)
    w.qed([fin], 'idi', S['zr341t'])
    return run8(w)


def mv(w, A, x, X, body, arg, mem, valc):
    """( A -> ( ( x e. X |-> body ) ` arg ) = body[x:=arg] ), valc proves ( A -> value e. CC )"""
    import congr as _cg
    val = tsub(body, {x: arg})
    ex = w.s([valc], 'elexd', '( %s -> %s e. _V )' % (A, val))
    st, v2 = _cg.mptval(w, A, x, X, body, arg, mem, exs=ex, gen=w.g)
    assert v2 == val, (v2, val)
    return st


def gen_341():
    w = W('zr341', 'Lean ` re_LSeries_vonMangoldt_comb_nonneg ` : ` 0 <_ 3 Re D ( X ) + 4 Re D ( X + i T ) + Re D ( X + 2 i T ) ` for the von Mangoldt series ` D ` on ` X > 1 ` ( ~ zr341t termwise, ~ zrisre , ~ zrsadd , ~ iserge0 ).')
    A0 = ante_of(S['zr341'])[0]
    c = Ctx(w, A0)
    xr = c.g('X e. RR'); x1 = c.g('1 < X'); tr = c.g('T e. RR')
    xc = c([xr], 'recnd', 'X e. CC'); tc = c([tr], 'recnd', 'T e. CC')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    t2r = c([numst8(w, A0, '2', 'RR'), tr], 'remulcld', '( 2 x. T ) e. RR')
    pts = {}
    for key, s_, im, imr in (('0', 'X', None, None), ('1', X1, 'T', tr), ('2', X2, '( 2 x. T )', t2r)):
        if im is None:
            sc = xc
            re_ = c([xr], 'rered', '( Re ` X ) = X')
        else:
            sc = c([xc, c([ic, c([imr], 'recnd', '%s e. CC' % im)], 'mulcld', '( _i x. %s ) e. CC' % im)], 'addcld', '%s e. CC' % s_)
            re_ = c([xr, imr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = X' % s_)
        s1 = c([x1, c([re_], 'eqcomd', 'X = ( Re ` %s )' % s_)], 'breqtrd', '1 < ( Re ` %s )' % s_)
        pts[key] = (s_, sc, s1)
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = c([], '1zzd', '1 e. ZZ')
    Aj = '( %s /\\ j e. NN )' % A0
    cj = Ctx(w, Aj)
    jn = cj([], 'simpr', 'j e. NN')
    An = '( %s /\\ n e. NN )' % A0
    cn = Ctx(w, An)
    nn_ = cn([], 'simpr', 'n e. NN')
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    def term_cc(ctx, A, v, vn, sc):
        lam = ctx([ctx([vn, w.inst('vmacl')], 'syl', '( Lam ` %s ) e. RR' % v)], 'recnd', '( Lam ` %s ) e. CC' % v)
        pw = ctx([ctx([vn], 'nncnd', '%s e. CC' % v), ctx([lift(w, sc, A)], 'negcld', '-u %s e. CC' % s_)], 'cxpcld', '( %s ^c -u %s ) e. CC' % (v, s_))
        return ctx([lam, pw], 'mulcld', '( ( Lam ` %s ) x. ( %s ^c -u %s ) ) e. CC' % (v, v, s_))
    R = {}
    for key in ('0', '1', '2'):
        s_, sc, s1 = pts[key]
        Fm = VMF(s_)
        B = '( ( Lam ` n ) x. ( n ^c -u %s ) )' % s_
        bn = term_cc(cn, An, 'n', nn_, sc)
        ffs = c([bn, w.s([], 'eqid', '%s = %s' % (Fm, Fm))], 'fmptd', '%s : NN --> CC' % Fm)
        cv = c([c([sc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (s_, s_)), w.inst('zrvmc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % Fm)
        zi = c([c([ffs, cv], 'jca', '( %s : NN --> CC /\\ seq 1 ( + , %s ) e. dom ~~> )' % (Fm, Fm)), w.inst('zrisre')], 'syl',
               '( ( Re ` sum_ k e. NN ( %s ` k ) ) = sum_ k e. NN ( Re ` ( %s ` k ) ) /\\ seq 1 ( + , ( Re o. %s ) ) e. dom ~~> )' % (Fm, Fm, Fm))
        zeq = c([zi], 'simpld', '( Re ` sum_ k e. NN ( %s ` k ) ) = sum_ k e. NN ( Re ` ( %s ` k ) )' % (Fm, Fm))
        zdm = c([zi], 'simprd', 'seq 1 ( + , ( Re o. %s ) ) e. dom ~~>' % Fm)
        # values at k (for the sums) and at j (for the series lemmas)
        fk = mv(w, Ak, 'n', 'NN', B, 'k', kn, term_cc(ck, Ak, 'k', kn, sc))
        fj = mv(w, Aj, 'n', 'NN', B, 'j', jn, term_cc(cj, Aj, 'j', jn, sc))
        TJ = '( ( Lam ` j ) x. ( j ^c -u %s ) )' % s_
        rco = cj([lift(w, ffs, Aj), jn, w.inst('fvco3')], 'syl2anc', '( ( Re o. %s ) ` j ) = ( Re ` ( %s ` j ) )' % (Fm, Fm))
        rj = cj([rco, cj([fj], 'fveq2d', '( Re ` ( %s ` j ) ) = ( Re ` %s )' % (Fm, TJ))], 'eqtrd', '( ( Re o. %s ) ` j ) = ( Re ` %s )' % (Fm, TJ))
        fjc = cj([lift(w, ffs, Aj), jn], 'ffvelcdmd', '( %s ` j ) e. CC' % Fm)
        rjr = cj([fjc], 'recld', '( Re ` ( %s ` j ) ) e. RR' % Fm)
        rck = ck([lift(w, ffs, Ak), kn, w.inst('fvco3')], 'syl2anc', '( ( Re o. %s ) ` k ) = ( Re ` ( %s ` k ) )' % (Fm, Fm))
        fkc = ck([lift(w, ffs, Ak), kn], 'ffvelcdmd', '( %s ` k ) e. CC' % Fm)
        rkr = ck([fkc], 'recld', '( Re ` ( %s ` k ) ) e. RR' % Fm)
        Q = 'sum_ k e. NN ( Re ` ( %s ` k ) )' % Fm
        lim = c([nnu, one, rck, ck([rkr], 'recnd', '( Re ` ( %s ` k ) ) e. CC' % Fm), zdm], 'isumclim2', 'seq 1 ( + , ( Re o. %s ) ) ~~> %s' % (Fm, Q))
        TK_ = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % s_
        se = c([fk], 'sumeq2dv', 'sum_ k e. NN ( %s ` k ) = sum_ k e. NN %s' % (Fm, TK_))
        qv = c([c([zeq], 'eqcomd', '%s = ( Re ` sum_ k e. NN ( %s ` k ) )' % (Q, Fm)), c([se], 'fveq2d', '( Re ` sum_ k e. NN ( %s ` k ) ) = ( Re ` %s )' % (Fm, DL(s_)))],
                'eqtrd', '%s = ( Re ` %s )' % (Q, DL(s_)))
        TJ = '( ( Lam ` j ) x. ( j ^c -u %s ) )' % s_
        rcj = cj([lift(w, ffs, Aj), jn, w.inst('fvco3')], 'syl2anc', '( ( Re o. %s ) ` j ) = ( Re ` ( %s ` j ) )' % (Fm, Fm))
        rj = cj([rcj, cj([fj], 'fveq2d', '( Re ` ( %s ` j ) ) = ( Re ` %s )' % (Fm, TJ))], 'eqtrd', '( ( Re o. %s ) ` j ) = ( Re ` %s )' % (Fm, TJ))
        fjc = cj([lift(w, ffs, Aj), jn], 'ffvelcdmd', '( %s ` j ) e. CC' % Fm)
        rjc = cj([rcj, cj([cj([fjc], 'recld', '( Re ` ( %s ` j ) ) e. RR' % Fm)], 'recnd', '( Re ` ( %s ` j ) ) e. CC' % Fm)], 'eqeltrd', '( ( Re o. %s ) ` j ) e. CC' % Fm)
        tkr = ck([term_cc(ck, Ak, 'k', kn, sc)], 'recld', '( Re ` %s ) e. RR' % TK_)
        tnr = cn([term_cc(cn, An, 'n', nn_, sc)], 'recld', '( Re ` ( ( Lam ` n ) x. ( n ^c -u %s ) ) ) e. RR' % s_)
        tjr = cj([term_cc(cj, Aj, 'j', jn, sc)], 'recld', '( Re ` %s ) e. RR' % TJ)
        R[key] = dict(Fm=Fm, ffs=ffs, lim=lim, rj=rj, rck=rck, fk=fk, Q=Q, qv=qv, TK=TK_, rjc=rjc, tkr=tkr, tnr=tnr, tjr=tjr, s=s_)
    RN = lambda key, v: '( Re ` ( ( Lam ` %s ) x. ( %s ^c -u %s ) ) )' % (v, v, R[key]['s'])
    # scaled series
    Gm = {}
    for key, m in (('0', '3'), ('1', '4')):
        r = R[key]
        B = '( %s x. %s )' % (m, RN(key, 'n'))
        Mp = '( n e. NN |-> %s )' % B
        mc = numst8(w, A0, m, 'CC')
        bj = cj([lift(w, mc, Aj), cj([r['tjr']], 'recnd', '%s e. CC' % RN(key, 'j'))], 'mulcld', '( %s x. %s ) e. CC' % (m, RN(key, 'j')))
        gj = mv(w, Aj, 'n', 'NN', B, 'j', jn, bj)
        gj2 = cj([gj, cj([r['rj']], 'oveq2d', '( %s x. ( ( Re o. %s ) ` j ) ) = ( %s x. %s )' % (m, r['Fm'], m, RN(key, 'j')))], 'eqtr4d',
                 '( %s ` j ) = ( %s x. ( ( Re o. %s ) ` j ) )' % (Mp, m, r['Fm']))
        lim = c([nnu, one, mc, r['lim'], r['rjc'], gj2], 'isermulc2', 'seq 1 ( + , %s ) ~~> ( %s x. %s )' % (Mp, m, r['Q']))
        bn = cn([lift(w, mc, An), cn([r['tnr']], 'recnd', '%s e. CC' % RN(key, 'n'))], 'mulcld', '%s e. CC' % B)
        fm = c([bn, w.s([], 'eqid', '%s = %s' % (Mp, Mp))], 'fmptd', '%s : NN --> CC' % Mp)
        bk = ck([lift(w, mc, Ak), ck([r['tkr']], 'recnd', '%s e. CC' % RN(key, 'k'))], 'mulcld', '( %s x. %s ) e. CC' % (m, RN(key, 'k')))
        gk = mv(w, Ak, 'n', 'NN', B, 'k', kn, bk)
        Gm[key] = dict(Mp=Mp, B=B, lim=lim, fm=fm, gk=gk, bk=bk, bn=bn, m=m)
    # H1 = G3 + G4
    B1 = '( %s + %s )' % (Gm['0']['B'], Gm['1']['B'])
    H1 = '( n e. NN |-> %s )' % B1
    b1n = cn([Gm['0']['bn'], Gm['1']['bn']], 'addcld', '%s e. CC' % B1)
    h1f = c([b1n, w.s([], 'eqid', '%s = %s' % (H1, H1))], 'fmptd', '%s : NN --> CC' % H1)
    V1k = tsub(B1, {'n': 'k'})
    b1k = ck([Gm['0']['bk'], Gm['1']['bk']], 'addcld', '%s e. CC' % V1k)
    h1k = mv(w, Ak, 'n', 'NN', B1, 'k', kn, b1k)
    h1e = ck([h1k, ck([Gm['0']['gk'], Gm['1']['gk']], 'oveq12d', '( ( %s ` k ) + ( %s ` k ) ) = %s' % (Gm['0']['Mp'], Gm['1']['Mp'], V1k))], 'eqtr4d',
             '( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) )' % (H1, Gm['0']['Mp'], Gm['1']['Mp']))
    al1 = c([h1e], 'ralrimiva', 'A. k e. NN ( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) )' % (H1, Gm['0']['Mp'], Gm['1']['Mp']))
    L1 = '( ( 3 x. %s ) + ( 4 x. %s ) )' % (R['0']['Q'], R['1']['Q'])
    ant1 = '( ( ( %s : NN --> CC /\\ %s : NN --> CC /\\ %s : NN --> CC ) /\\ A. k e. NN ( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) ) ) /\\ ( seq 1 ( + , %s ) ~~> ( 3 x. %s ) /\\ seq 1 ( + , %s ) ~~> ( 4 x. %s ) ) )' % (
        Gm['0']['Mp'], Gm['1']['Mp'], H1, H1, Gm['0']['Mp'], Gm['1']['Mp'], Gm['0']['Mp'], R['0']['Q'], Gm['1']['Mp'], R['1']['Q'])
    a1 = c([c([c([Gm['0']['fm'], Gm['1']['fm'], h1f], '3jca', '( %s : NN --> CC /\\ %s : NN --> CC /\\ %s : NN --> CC )' % (Gm['0']['Mp'], Gm['1']['Mp'], H1)), al1], 'jca', top_and(ant1)[0]),
            c([Gm['0']['lim'], Gm['1']['lim']], 'jca', top_and(ant1)[1])], 'jca', ant1)
    lim1 = c([a1, w.inst('zrsadd')], 'syl', 'seq 1 ( + , %s ) ~~> %s' % (H1, L1))
    # H2 = H1 + Re o. F_X2
    r2 = R['2']
    B2 = '( %s + %s )' % (B1, RN('2', 'n'))
    H2 = '( n e. NN |-> %s )' % B2
    b2n = cn([b1n, cn([r2['tnr']], 'recnd', '%s e. CC' % RN('2', 'n'))], 'addcld', '%s e. CC' % B2)
    h2f = c([b2n, w.s([], 'eqid', '%s = %s' % (H2, H2))], 'fmptd', '%s : NN --> CC' % H2)
    ref = c.a1(w.s([], 'ref', 'Re : CC --> RR'), 'Re : CC --> RR')
    rfr = c([ref, r2['ffs'], w.inst('fco')], 'syl2anc', '( Re o. %s ) : NN --> RR' % r2['Fm'])
    rfc = c([rfr, c.a1(w.s([], 'ax-resscn', 'RR C_ CC'), 'RR C_ CC')], 'fssd', '( Re o. %s ) : NN --> CC' % r2['Fm'])
    V2k = tsub(B2, {'n': 'k'})
    b2k = ck([b1k, ck([r2['tkr']], 'recnd', '%s e. CC' % RN('2', 'k'))], 'addcld', '%s e. CC' % V2k)
    h2k = mv(w, Ak, 'n', 'NN', B2, 'k', kn, b2k)
    rk2 = ck([r2['rck'], ck([r2['fk']], 'fveq2d', '( Re ` ( %s ` k ) ) = %s' % (r2['Fm'], RN('2', 'k')))], 'eqtrd', '( ( Re o. %s ) ` k ) = %s' % (r2['Fm'], RN('2', 'k')))
    h2e = ck([h2k, ck([h1k, rk2], 'oveq12d', '( ( %s ` k ) + ( ( Re o. %s ) ` k ) ) = %s' % (H1, r2['Fm'], V2k))], 'eqtr4d',
             '( %s ` k ) = ( ( %s ` k ) + ( ( Re o. %s ) ` k ) )' % (H2, H1, r2['Fm']))
    al2 = c([h2e], 'ralrimiva', 'A. k e. NN ( %s ` k ) = ( ( %s ` k ) + ( ( Re o. %s ) ` k ) )' % (H2, H1, r2['Fm']))
    L2 = '( %s + %s )' % (L1, r2['Q'])
    ant2 = '( ( ( %s : NN --> CC /\\ ( Re o. %s ) : NN --> CC /\\ %s : NN --> CC ) /\\ A. k e. NN ( %s ` k ) = ( ( %s ` k ) + ( ( Re o. %s ) ` k ) ) ) /\\ ( seq 1 ( + , %s ) ~~> %s /\\ seq 1 ( + , ( Re o. %s ) ) ~~> %s ) )' % (
        H1, r2['Fm'], H2, H2, H1, r2['Fm'], H1, L1, r2['Fm'], r2['Q'])
    a2 = c([c([c([h1f, rfc, h2f], '3jca', top_and(top_and(ant2)[0])[0]), al2], 'jca', top_and(ant2)[0]), c([lim1, r2['lim']], 'jca', top_and(ant2)[1])], 'jca', ant2)
    lim2 = c([a2, w.inst('zrsadd')], 'syl', 'seq 1 ( + , %s ) ~~> %s' % (H2, L2))
    # nonnegativity
    V2j = tsub(B2, {'n': 'j'})
    t341 = cj([cj([jn, cj([lift(w, xr, Aj), lift(w, tr, Aj)], 'jca', '( X e. RR /\\ T e. RR )')], 'jca', '( j e. NN /\\ ( X e. RR /\\ T e. RR ) )'), w.inst('zr341t')], 'syl', '0 <_ %s' % V2j)
    lvj = {RN('0', 'j'): R['0']['tjr'], RN('1', 'j'): R['1']['tjr'], RN('2', 'j'): R['2']['tjr']}
    clj = Closure(w, Aj, lvj)
    v2jr = clj.mem(V2j, 'RR')
    h2j = mv(w, Aj, 'n', 'NN', B2, 'j', jn, cj([v2jr], 'recnd', '%s e. CC' % V2j))
    hjr = cj([h2j, v2jr], 'eqeltrd', '( %s ` j ) e. RR' % H2)
    hj0 = cj([t341, h2j], 'breqtrrd', '0 <_ ( %s ` j )' % H2)
    ge = c([nnu, one, lim2, hjr, hj0], 'iserge0', '0 <_ %s' % L2)
    GOAL = ante_of(S['zr341'])[1]
    RHS = GOAL[len('0 <_ '):]
    e3 = c([c([c([R['0']['qv']], 'oveq2d', '( 3 x. %s ) = ( 3 x. ( Re ` %s ) )' % (R['0']['Q'], DL('X'))), c([R['1']['qv']], 'oveq2d', '( 4 x. %s ) = ( 4 x. ( Re ` %s ) )' % (R['1']['Q'], DL(X1)))],
              'oveq12d', '%s = ( ( 3 x. ( Re ` %s ) ) + ( 4 x. ( Re ` %s ) ) )' % (L1, DL('X'), DL(X1))), R['2']['qv']], 'oveq12d', '%s = %s' % (L2, RHS))
    fin = c([ge, e3], 'breqtrd', GOAL)
    w.qed([fin], 'idi', S['zr341'])
    return run8(w)


GENS = {'zrvmc': gen_vmc, 'zr341t': gen_341t, 'zr341': gen_341}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
