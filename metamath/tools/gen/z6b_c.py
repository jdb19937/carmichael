"""Sortie Z6b, section 4: the anchor identity's algebra and bounds.
z6acoef  | a(K) psi_r(K) C(K) K ^ -S | <_ K R
z6aterm  ( G X ^ W ) ( A Y ^ -u ( S + W ) ) = ( A Y ^ -u S ) ( G ( Y / X ) ^ -u W )
z6nx     N ( N / X ) ^ -u 3 = X ^ 3 N ^ -u 2
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_c.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift
from z6a_e3 import conjs, build, unpack, c_
from z6b_m import inst_all
import lin
from lin import linarith
import num

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def z6acoef():
    w = W('z6acoef', 'The detector coefficient times ` K ^ -u S ` is at most ` K R ` in absolute value (~ z5bvaabs , ~ z5psiabs , ` | C | <_ 1 ` , '
          '` Re S >_ 0 ` ).')
    a = ante('z6acoef'); f = unpack(w, a); st = mkst(w, a)
    kn = f['K e. NN']; sc = f['S e. CC']; rs0 = f['0 <_ ( Re ` S )']
    BV = '( ( A bvA B ) ` K )'; PS = '( ( mmu ` ( R gcd K ) ) x. ( phi ` ( R gcd K ) ) )'; CK = '( C ` K )'; KS = '( K ^c -u S )'
    f['N e. NN'] = kn
    p1, _ = applyn(w, a, 'z5bvaabs', {'N': 'K'}, f)
    p2 = st([f['R e. NN'], kn, w.inst('z5psiabs')], 'syl2anc', '( abs ` %s ) <_ R' % PS)
    p3, _ = inst_all(w, a, f[CB], 'j', 'NN', '( abs ` ( C ` j ) ) <_ 1', 'K', kn)
    bc = st([p1, w.inst('z6absle')], 'syl', '%s e. CC' % BV)
    pc = st([p2, w.inst('z6absle')], 'syl', '%s e. CC' % PS)
    cc = st([p3, w.inst('z6absle')], 'syl', '%s e. CC' % CK)
    krp = st([kn], 'nnrpd', 'K e. RR+'); kr = st([kn], 'nnred', 'K e. RR'); kc = st([kn], 'nncnd', 'K e. CC')
    nsc = st([sc], 'negcld', '-u S e. CC')
    ksc = st([kc, nsc], 'cxpcld', '%s e. CC' % KS)
    ak = st([krp, nsc, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( K ^c ( Re ` -u S ) )' % KS)
    rn = st([sc, w.inst('reneg')], 'syl', '( Re ` -u S ) = -u ( Re ` S )')
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    le0 = linarith(w, a, [rs0], '-u ( Re ` S ) <_ 0', leaves={'( Re ` S )': rsr})
    k1 = st([kn], 'nnge1d', '1 <_ K')
    cl = st([kr, k1, st([rsr], 'renegcld', '-u ( Re ` S ) e. RR'), c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), le0], 'cxplead', '( K ^c -u ( Re ` S ) ) <_ ( K ^c 0 )')
    k0 = st([kc, w.inst('cxp0')], 'syl', '( K ^c 0 ) = 1')
    p4 = st([st([ak, st([rn], 'oveq2d', '( K ^c ( Re ` -u S ) ) = ( K ^c -u ( Re ` S ) )')], 'eqtrd', '( abs ` %s ) = ( K ^c -u ( Re ` S ) )' % KS),
             st([cl, k0], 'breqtrd', '( K ^c -u ( Re ` S ) ) <_ 1')], 'eqbrtrd', '( abs ` %s ) <_ 1' % KS)
    X1 = '( %s x. %s )' % (BV, PS); X2 = '( %s x. %s )' % (X1, CK)
    x1c = st([bc, pc], 'mulcld', '%s e. CC' % X1); x2c = st([x1c, cc], 'mulcld', '%s e. CC' % X2)
    e1 = st([x2c, ksc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X2, KS, X2, KS))
    e2 = st([x1c, cc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X2, X1, CK))
    e3 = st([bc, pc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X1, BV, PS))
    ab = lambda E, c_step: (st([c_step], 'abscld', '( abs ` %s ) e. RR' % E), st([c_step], 'absge0d', '0 <_ ( abs ` %s )' % E))
    (br, b0), (pr, p0), (cr, c0), (xr, x0) = ab(BV, bc), ab(PS, pc), ab(CK, cc), ab(KS, ksc)
    rr = st([f['R e. NN']], 'nnred', 'R e. RR')
    one = c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')
    m1 = st([br, kr, pr, rr, b0, p0, p1, p2], 'lemul12ad', '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( K x. R )' % (BV, PS))
    AX1 = '( ( abs ` %s ) x. ( abs ` %s ) )' % (BV, PS)
    ax1r = st([br, pr], 'remulcld', '%s e. RR' % AX1); ax10 = st([br, pr, b0, p0], 'mulge0d', '0 <_ %s' % AX1)
    krr = st([kr, rr], 'remulcld', '( K x. R ) e. RR')
    m2 = st([ax1r, krr, cr, one, ax10, c0, m1, p3], 'lemul12ad', '( %s x. ( abs ` %s ) ) <_ ( ( K x. R ) x. 1 )' % (AX1, CK))
    AX2 = '( %s x. ( abs ` %s ) )' % (AX1, CK)
    ax2r = st([ax1r, cr], 'remulcld', '%s e. RR' % AX2); ax20 = st([ax1r, cr, ax10, c0], 'mulge0d', '0 <_ %s' % AX2)
    kr1 = st([krr, one], 'remulcld', '( ( K x. R ) x. 1 ) e. RR')
    m3 = st([ax2r, kr1, xr, one, ax20, x0, m2, p4], 'lemul12ad', '( %s x. ( abs ` %s ) ) <_ ( ( ( K x. R ) x. 1 ) x. 1 )' % (AX2, KS))
    eqa = st([e1, st([st([e2, st([e3], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = %s' % (X1, CK, AX2))], 'eqtrd', '( abs ` %s ) = %s' % (X2, AX2))], 'oveq1d',
                     '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (X2, KS, AX2, KS))], 'eqtrd', '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (X2, KS, AX2, KS))
    krc = st([krr], 'recnd', '( K x. R ) e. CC')
    s1 = st([st([st([krc], 'mulridd', '( ( K x. R ) x. 1 ) = ( K x. R )')], 'oveq1d', '( ( ( K x. R ) x. 1 ) x. 1 ) = ( ( K x. R ) x. 1 )'), st([krc], 'mulridd', '( ( K x. R ) x. 1 ) = ( K x. R )')],
            'eqtrd', '( ( ( K x. R ) x. 1 ) x. 1 ) = ( K x. R )')
    w.qed([st([eqa, m3], 'eqbrtrd', '( abs ` ( %s x. %s ) ) <_ ( ( ( K x. R ) x. 1 ) x. 1 )' % (X2, KS)), s1], 'breqtrd', STATEMENTS['z6acoef'])
    return w


def z6aterm():
    w = W('z6aterm', 'The Mellin term identity (Lean ` Fterm_eq_term ` ): ` ( G X ^ W ) ( A Y ^ -u ( S + W ) ) = ( A Y ^ -u S ) ( G ( Y / X ) ^ -u W ) ` '
          'for positive reals ` X ` , ` Y ` (~ cxpaddd , ~ divcxpd , ~ cxpnegd ).')
    a = ante('z6aterm'); f = unpack(w, a); st = mkst(w, a)
    yrp = f['Y e. RR+']; xrp = f['X e. RR+']; sc = f['S e. CC']; wc = f['W e. CC']; ac = f['A e. CC']; gc = f['G e. CC']
    yc = st([yrp], 'rpcnd', 'Y e. CC'); yn = st([yrp], 'rpne0d', 'Y =/= 0'); xc = st([xrp], 'rpcnd', 'X e. CC'); xn = st([xrp], 'rpne0d', 'X =/= 0')
    ns = st([sc], 'negcld', '-u S e. CC'); nw = st([wc], 'negcld', '-u W e. CC')
    p = '( X ^c W )'; q = '( Y ^c -u S )'; r = '( Y ^c -u W )'
    pc = st([xc, wc], 'cxpcld', '%s e. CC' % p); qc = st([yc, ns], 'cxpcld', '%s e. CC' % q); rc = st([yc, nw], 'cxpcld', '%s e. CC' % r)
    pn = st([xc, xn, wc], 'cxpne0d', '%s =/= 0' % p)
    e1 = st([st([sc, wc], 'negdid', '-u ( S + W ) = ( -u S + -u W )')], 'oveq2d', '( Y ^c -u ( S + W ) ) = ( Y ^c ( -u S + -u W ) )')
    e2 = st([yc, yn, ns, nw], 'cxpaddd', '( Y ^c ( -u S + -u W ) ) = ( %s x. %s )' % (q, r))
    L0 = '( ( G x. %s ) x. ( A x. ( Y ^c -u ( S + W ) ) ) )' % p
    e3 = st([st([e1, e2], 'eqtrd', '( Y ^c -u ( S + W ) ) = ( %s x. %s )' % (q, r))], 'oveq2d', '( A x. ( Y ^c -u ( S + W ) ) ) = ( A x. ( %s x. %s ) )' % (q, r))
    GP = '( G x. %s )' % p; AQ = '( A x. %s )' % q
    e4 = st([e3], 'oveq2d', '%s = ( %s x. ( A x. ( %s x. %s ) ) )' % (L0, GP, q, r))
    e5 = st([st([st([ac, qc, rc], 'mulassd', '( %s x. %s ) = ( A x. ( %s x. %s ) )' % (AQ, r, q, r))], 'eqcomd', '( A x. ( %s x. %s ) ) = ( %s x. %s )' % (q, r, AQ, r))],
            'oveq2d', '( %s x. ( A x. ( %s x. %s ) ) ) = ( %s x. ( %s x. %s ) )' % (GP, q, r, GP, AQ, r))
    gpc = st([gc, pc], 'mulcld', '%s e. CC' % GP); aqc = st([ac, qc], 'mulcld', '%s e. CC' % AQ)
    e6 = st([gpc, aqc, rc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (GP, AQ, r, AQ, GP, r))
    e7 = st([st([gc, pc, rc], 'mulassd', '( %s x. %s ) = ( G x. ( %s x. %s ) )' % (GP, r, p, r)), st([st([pc, rc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (p, r, r, p))], 'oveq2d',
                                                                                              '( G x. ( %s x. %s ) ) = ( G x. ( %s x. %s ) )' % (p, r, r, p))], 'eqtrd',
            '( %s x. %s ) = ( G x. ( %s x. %s ) )' % (GP, r, r, p))
    e8 = st([e7], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( G x. ( %s x. %s ) ) )' % (AQ, GP, r, AQ, r, p))
    lhs = st([st([st([e4, e5], 'eqtrd', '%s = ( %s x. ( %s x. %s ) )' % (L0, GP, AQ, r)), e6], 'eqtrd', '%s = ( %s x. ( %s x. %s ) )' % (L0, AQ, GP, r)), e8], 'eqtrd',
             '%s = ( %s x. ( G x. ( %s x. %s ) ) )' % (L0, AQ, r, p))
    # ( Y / X ) ^ -u W = r x. p
    YX = '( ( Y / X ) ^c -u W )'
    d1 = st([st([yrp], 'rpred', 'Y e. RR'), st([yrp], 'rpge0d', '0 <_ Y'), xrp, nw], 'divcxpd', '%s = ( %s / ( X ^c -u W ) )' % (YX, r))
    d2 = st([xc, xn, wc], 'cxpnegd', '( X ^c -u W ) = ( 1 / %s )' % p)
    d3 = st([d2], 'oveq2d', '( %s / ( X ^c -u W ) ) = ( %s / ( 1 / %s ) )' % (r, r, p))
    rpn = st([pc, pn], 'reccld', '( 1 / %s ) e. CC' % p); rpn0 = st([pc, pn], 'recne0d', '( 1 / %s ) =/= 0' % p)
    d4 = st([rc, rpn, rpn0], 'divrecd', '( %s / ( 1 / %s ) ) = ( %s x. ( 1 / ( 1 / %s ) ) )' % (r, p, r, p))
    d5 = st([st([pc, pn], 'recrecd', '( 1 / ( 1 / %s ) ) = %s' % (p, p))], 'oveq2d', '( %s x. ( 1 / ( 1 / %s ) ) ) = ( %s x. %s )' % (r, p, r, p))
    yx = st([st([st([d1, d3], 'eqtrd', '%s = ( %s / ( 1 / %s ) )' % (YX, r, p)), d4], 'eqtrd', '%s = ( %s x. ( 1 / ( 1 / %s ) ) )' % (YX, r, p)), d5], 'eqtrd',
            '%s = ( %s x. %s )' % (YX, r, p))
    rhs = st([st([yx], 'oveq2d', '( G x. %s ) = ( G x. ( %s x. %s ) )' % (YX, r, p))], 'oveq2d', '( %s x. ( G x. %s ) ) = ( %s x. ( G x. ( %s x. %s ) ) )' % (AQ, YX, AQ, r, p))
    w.qed([lhs, rhs], 'eqtr4d', STATEMENTS['z6aterm'])
    return w


def z6nx():
    w = W('z6nx', '` N ( N / X ) ^ -u 3 = X ^ 3 N ^ -u 2 ` for positive reals (~ divcxpd , ~ cxpnegd , ~ cxpaddd ).')
    a = ante('z6nx'); st = mkst(w, a)
    nrp = st([], 'simpl', 'N e. RR+'); xrp = st([], 'simpr', 'X e. RR+')
    nc = st([nrp], 'rpcnd', 'N e. CC'); nn0 = st([nrp], 'rpne0d', 'N =/= 0'); xc = st([xrp], 'rpcnd', 'X e. CC'); xn = st([xrp], 'rpne0d', 'X =/= 0')
    three = c_(w, a, w.s([], '3cn', '3 e. CC'), '3 e. CC'); n3 = st([three], 'negcld', '-u 3 e. CC')
    P = '( X ^c 3 )'; Q = '( N ^c -u 3 )'
    pc = st([xc, three], 'cxpcld', '%s e. CC' % P); pn = st([xc, xn, three], 'cxpne0d', '%s =/= 0' % P)
    qc = st([nc, n3], 'cxpcld', '%s e. CC' % Q)
    d1 = st([st([nrp], 'rpred', 'N e. RR'), st([nrp], 'rpge0d', '0 <_ N'), xrp, n3], 'divcxpd', '( ( N / X ) ^c -u 3 ) = ( %s / ( X ^c -u 3 ) )' % Q)
    d2 = st([st([xc, xn, three], 'cxpnegd', '( X ^c -u 3 ) = ( 1 / %s )' % P)], 'oveq2d', '( %s / ( X ^c -u 3 ) ) = ( %s / ( 1 / %s ) )' % (Q, Q, P))
    rp = st([pc, pn], 'reccld', '( 1 / %s ) e. CC' % P); rp0 = st([pc, pn], 'recne0d', '( 1 / %s ) =/= 0' % P)
    d3 = st([qc, rp, rp0], 'divrecd', '( %s / ( 1 / %s ) ) = ( %s x. ( 1 / ( 1 / %s ) ) )' % (Q, P, Q, P))
    d4 = st([st([pc, pn], 'recrecd', '( 1 / ( 1 / %s ) ) = %s' % (P, P))], 'oveq2d', '( %s x. ( 1 / ( 1 / %s ) ) ) = ( %s x. %s )' % (Q, P, Q, P))
    nx = st([st([st([d1, d2], 'eqtrd', '( ( N / X ) ^c -u 3 ) = ( %s / ( 1 / %s ) )' % (Q, P)), d3], 'eqtrd', '( ( N / X ) ^c -u 3 ) = ( %s x. ( 1 / ( 1 / %s ) ) )' % (Q, P)), d4],
            'eqtrd', '( ( N / X ) ^c -u 3 ) = ( %s x. %s )' % (Q, P))
    e1 = st([nx], 'oveq2d', '( N x. ( ( N / X ) ^c -u 3 ) ) = ( N x. ( %s x. %s ) )' % (Q, P))
    e2 = st([st([nc, qc, pc], 'mulassd', '( ( N x. %s ) x. %s ) = ( N x. ( %s x. %s ) )' % (Q, P, Q, P))], 'eqcomd', '( N x. ( %s x. %s ) ) = ( ( N x. %s ) x. %s )' % (Q, P, Q, P))
    # N x. N ^ -u 3 = N ^ -u 2
    one = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    c1 = st([nc, w.inst('cxp1')], 'syl', '( N ^c 1 ) = N')
    ad = st([nc, nn0, one, n3], 'cxpaddd', '( N ^c ( 1 + -u 3 ) ) = ( ( N ^c 1 ) x. %s )' % Q)
    m32 = lin.lineq(w, a, '( 1 + -u 3 )', '-u 2', leaves={})
    ad2 = st([st([st([m32], 'oveq2d', '( N ^c ( 1 + -u 3 ) ) = ( N ^c -u 2 )')], 'eqcomd', '( N ^c -u 2 ) = ( N ^c ( 1 + -u 3 ) )'), ad], 'eqtrd', '( N ^c -u 2 ) = ( ( N ^c 1 ) x. %s )' % Q)
    ad3 = st([ad2, st([c1], 'oveq1d', '( ( N ^c 1 ) x. %s ) = ( N x. %s )' % (Q, Q))], 'eqtrd', '( N ^c -u 2 ) = ( N x. %s )' % Q)
    e3 = st([st([ad3], 'eqcomd', '( N x. %s ) = ( N ^c -u 2 )' % Q)], 'oveq1d', '( ( N x. %s ) x. %s ) = ( ( N ^c -u 2 ) x. %s )' % (Q, P, P))
    n2c = st([nc, st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC')], 'negcld', '-u 2 e. CC')], 'cxpcld', '( N ^c -u 2 ) e. CC')
    e4 = st([n2c, pc], 'mulcomd', '( ( N ^c -u 2 ) x. %s ) = ( %s x. ( N ^c -u 2 ) )' % (P, P))
    w.qed([st([st([e1, e2], 'eqtrd', '( N x. ( ( N / X ) ^c -u 3 ) ) = ( ( N x. %s ) x. %s )' % (Q, P)), e3], 'eqtrd', '( N x. ( ( N / X ) ^c -u 3 ) ) = ( ( N ^c -u 2 ) x. %s )' % P), e4],
          'eqtrd', STATEMENTS['z6nx'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6acoef, z6aterm, z6nx]:
        if want(fn.__name__):
            if not run(fn()):
                break
