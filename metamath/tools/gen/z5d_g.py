"""Sortie Z5d, section G: the Gamma strip bound I8(b) (Detection.lean 85-228), from set.mm's Euler product gamcvg2."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5dlib import *
from cl import Closure, lift, split_imp, formula_of
import lin
import num


def cn(w, step):
    return split_imp(formula_of(w, step))[1]


def adr(w, step, ante):
    """( A -> P ) to ( ( A /\\ x ) -> P ) where ante = ( A /\\ x )"""
    return w.s([step], 'adantr', '( %s -> %s )' % (ante, cn(w, step)))


def z5dbern():
    w = W('z5dbern', "Bernoulli's inequality for exponents in [ 0 , 1 ]: A ^ X <_ 1 + X ( A - 1 ) for A >_ 1 (the convexity of exp, "
                     "set.mm's efcvx, at the endpoints 0 and log A).  It bounds the real part of the Euler-product factor of Gamma.")
    a = '( ( A e. RR /\\ 1 <_ A ) /\\ ( X e. RR /\\ ( 0 <_ X /\\ X <_ 1 ) ) )'
    st = mkst(w, a)
    ar = st([], 'simpll', 'A e. RR'); a1_ = st([], 'simplr', '1 <_ A'); xr = st([], 'simprl', 'X e. RR')
    x0 = st([st([], 'simprr', '( 0 <_ X /\\ X <_ 1 )')], 'simpld', '0 <_ X'); x1 = st([st([], 'simprr', '( 0 <_ X /\\ X <_ 1 )')], 'simprd', 'X <_ 1')
    arp = st([ar, lin.linarith(w, a, [a1_], '0 < A', leaves={'A': ('RR', ar)})], 'elrpd', 'A e. RR+')
    AX = '( A ^c X )'
    axr = st([st([arp, xr], 'rpcxpcld', '%s e. RR+' % AX)], 'rpred', '%s e. RR' % AX)
    RHS = '( 1 + ( X x. ( A - 1 ) ) )'
    GOAL = '%s <_ %s' % (AX, RHS)
    lv = lambda ante: {'A': ('RR', adr_(ante, ar)), 'X': ('RR', adr_(ante, xr)), AX: ('RR', adr_(ante, axr))}

    def adr_(ante, step):
        return lift(w, step, ante)

    def fin(ante, hyps):
        cl = Closure(w, ante, lv(ante)); cl.atom(AX)
        return lin.linarith(w, ante, hyps, GOAL, closure=cl, products=True)
    # A = 1
    c1 = '( %s /\\ A = 1 )' % a
    s1 = mkst(w, c1)
    ea = s1([], 'simpr', 'A = 1')
    e1 = s1([s1([ea], 'oveq1d', '%s = ( 1 ^c X )' % AX), sy(w, c1, s1([adr_(c1, xr)], 'recnd', 'X e. CC'), '1cxp', '( 1 ^c X ) = 1')], 'eqtrd', '%s = 1' % AX)
    e2 = s1([s1([ea], 'oveq1d', '( A - 1 ) = ( 1 - 1 )')], 'oveq2d', '( X x. ( A - 1 ) ) = ( X x. ( 1 - 1 ) )')
    g1 = fin(c1, [e1, e2])
    # A > 1
    c2 = '( %s /\\ -. A = 1 )' % a
    s2 = mkst(w, c2)
    an1 = s2([s2([], 'simpr', '-. A = 1')], 'neqned', 'A =/= 1')
    agt = s2([s2([adr_(c2, a1_), an1], 'jca', '( 1 <_ A /\\ A =/= 1 )'), s2([s2([], '1red', '1 e. RR'), adr_(c2, ar), w.inst('ltlen')], 'syl2anc', '( 1 < A <-> ( 1 <_ A /\\ A =/= 1 ) )')],
             'mpbird', '1 < A')
    #   X = 0
    c3 = '( %s /\\ X = 0 )' % c2
    s3 = mkst(w, c3)
    ex0 = s3([], 'simpr', 'X = 0')
    e3 = s3([s3([ex0], 'oveq2d', '%s = ( A ^c 0 )' % AX), sy(w, c3, s3([adr_(c3, ar)], 'recnd', 'A e. CC'), 'cxp0', '( A ^c 0 ) = 1')], 'eqtrd', '%s = 1' % AX)
    e4 = s3([ex0], 'oveq1d', '( X x. ( A - 1 ) ) = ( 0 x. ( A - 1 ) )')
    g3 = fin(c3, [e3, e4])
    #   X = 1
    c4 = '( %s /\\ -. X = 0 )' % c2
    s4 = mkst(w, c4)
    c5 = '( %s /\\ X = 1 )' % c4
    s5 = mkst(w, c5)
    ex1 = s5([], 'simpr', 'X = 1')
    e5 = s5([s5([ex1], 'oveq2d', '%s = ( A ^c 1 )' % AX), sy(w, c5, s5([adr_(c5, ar)], 'recnd', 'A e. CC'), 'cxp1', '( A ^c 1 ) = A')], 'eqtrd', '%s = A' % AX)
    e6 = s5([ex1], 'oveq1d', '( X x. ( A - 1 ) ) = ( 1 x. ( A - 1 ) )')
    g5 = fin(c5, [e5, e6])
    #   0 < X < 1: efcvx
    c6 = '( %s /\\ -. X = 1 )' % c4
    s6 = mkst(w, c6)
    L_ = lambda s: lift(w, s, c6)
    xr6 = L_(xr)
    xn0 = s6([L_(s4([], 'simpr', '-. X = 0'))], 'neqned', 'X =/= 0')
    xp = s6([s6([L_(x0), xn0], 'jca', '( 0 <_ X /\\ X =/= 0 )'), s6([s6([], '0red', '0 e. RR'), xr6, w.inst('ltlen')], 'syl2anc', '( 0 < X <-> ( 0 <_ X /\\ X =/= 0 ) )')],
            'mpbird', '0 < X')
    x1n = s6([s6([s6([], 'simpr', '-. X = 1')], 'neqned', 'X =/= 1')], 'necomd', '1 =/= X')
    xl = s6([s6([L_(x1), x1n], 'jca', '( X <_ 1 /\\ 1 =/= X )'), s6([xr6, s6([], '1red', '1 e. RR'), w.inst('ltlen')], 'syl2anc', '( X < 1 <-> ( X <_ 1 /\\ 1 =/= X ) )')],
            'mpbird', 'X < 1')
    T = '( 1 - X )'
    tr = s6([s6([], '1red', '1 e. RR'), xr6], 'resubcld', '%s e. RR' % T)
    t0 = lin.linarith(w, c6, [xl], '0 < %s' % T, leaves={'X': ('RR', xr6)})
    t1 = lin.linarith(w, c6, [xp], '%s < 1' % T, leaves={'X': ('RR', xr6)})
    tio = s6([s6([tr, t0, t1], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s < 1 )' % (T, T, T)),
              a1(w, c6, w.s([w.s([], '0xr', '0 e. RR*'), w.s([], '1xr', '1 e. RR*'), w.inst('elioo2')], 'mp2an', '( %s e. ( 0 (,) 1 ) <-> ( %s e. RR /\\ 0 < %s /\\ %s < 1 ) )' % (T, T, T, T)),
                 '( %s e. ( 0 (,) 1 ) <-> ( %s e. RR /\\ 0 < %s /\\ %s < 1 ) )' % (T, T, T, T))], 'mpbird', '%s e. ( 0 (,) 1 )' % T)
    L = '( log ` A )'
    arp6 = L_(arp)
    lr = s6([arp6], 'relogcld', '%s e. RR' % L)
    agt6 = lift(w, agt, c6)
    llt = s6([agt6, s6([a1(w, c6, w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), arp6, w.inst('logltb')], 'syl2anc', '( 1 < A <-> ( log ` 1 ) < %s )' % L)], 'mpbid',
             '( log ` 1 ) < %s' % L)
    l0 = s6([a1(w, c6, w.s([], 'log1', '( log ` 1 ) = 0'), '( log ` 1 ) = 0'), llt], 'eqbrtrrd', '0 < %s' % L)
    ARG = '( ( %s x. 0 ) + ( ( 1 - %s ) x. %s ) )' % (T, T, L)
    RH = '( ( %s x. ( exp ` 0 ) ) + ( ( 1 - %s ) x. ( exp ` %s ) ) )' % (T, T, L)
    cvx = s6([s6([s6([], '0red', '0 e. RR'), lr, l0], '3jca', '( 0 e. RR /\\ %s e. RR /\\ 0 < %s )' % (L, L)), tio, w.inst('efcvx')], 'syl2anc',
             '( exp ` %s ) < %s' % (ARG, RH))
    m0 = s6([s6([tr], 'recnd', '%s e. CC' % T)], 'mul01d', '( %s x. 0 ) = 0' % T)
    nc = s6([s6([], '1cnd', '1 e. CC'), s6([xr6], 'recnd', 'X e. CC')], 'nncand', '( 1 - %s ) = X' % T)
    ra, na = w.rewrite(ARG, {'( %s x. 0 )' % T: ('0', m0), '( 1 - %s )' % T: ('X', nc)}, c6)
    argeq = s6([ra, s6([s6([s6([xr6, lr], 'remulcld', '( X x. %s ) e. RR' % L)], 'recnd', '( X x. %s ) e. CC' % L)], 'addlidd', '%s = ( X x. %s )' % (na, L))], 'eqtrd',
               '%s = ( X x. %s )' % (ARG, L))
    cx = s6([s6([arp6], 'rpcnd', 'A e. CC'), s6([arp6], 'rpne0d', 'A =/= 0'), s6([xr6], 'recnd', 'X e. CC'), w.inst('cxpef')], 'syl3anc', '%s = ( exp ` ( X x. %s ) )' % (AX, L))
    lhs = s6([s6([argeq], 'fveq2d', '( exp ` %s ) = ( exp ` ( X x. %s ) )' % (ARG, L)), cx], 'eqtr4d', '( exp ` %s ) = %s' % (ARG, AX))
    r0 = a1(w, c6, w.s([], 'ef0', '( exp ` 0 ) = 1'), '( exp ` 0 ) = 1')
    rl = sy(w, c6, arp6, 'reeflog', '( exp ` %s ) = A' % L)
    rw, new = w.rewrite(RH, {'( exp ` 0 )': ('1', r0), '( exp ` %s )' % L: ('A', rl), '( 1 - %s )' % T: ('X', nc)}, c6)
    cvx2 = s6([cvx, lhs, rw], '3brtr3d', '%s < %s' % (AX, new))
    g6 = fin(c6, [cvx2])
    g4 = w.s([g5, g6], 'pm2.61dan', '( %s -> %s )' % (c4, GOAL))
    g2 = w.s([g3, g4], 'pm2.61dan', '( %s -> %s )' % (c2, GOAL))
    w.qed([g1, g2], 'pm2.61dan', STATEMENTS['z5dbern'])
    return w


def zfacts(w, a, zc, x0, x1, m, mn, st):
    """for Z e. CC with 0 <_ Re Z <_ 1 and m e. NN: Re ( Z + m ) = m + Re Z, ( m + Re Z ) <_ | Z + m |, 0 < | Z + m |, Z + m =/= 0"""
    xr = st([zc], 'recld', '%s e. RR' % RZ)
    mc = st([mn], 'nncnd', '%s e. CC' % m)
    zm = '( Z + %s )' % m
    zmc = st([zc, mc], 'addcld', '%s e. CC' % zm)
    re1 = st([zc, mc, w.inst('readd')], 'syl2anc', '( Re ` %s ) = ( %s + ( Re ` %s ) )' % (zm, RZ, m))
    re2 = sy(w, a, st([mn], 'nnred', '%s e. RR' % m), 'rere', '( Re ` %s ) = %s' % (m, m))
    re = st([re1, st([re2], 'oveq2d', '( %s + ( Re ` %s ) ) = ( %s + %s )' % (RZ, m, RZ, m)),
              st([st([xr], 'recnd', '%s e. CC' % RZ), mc], 'addcomd', '( %s + %s ) = ( %s + %s )' % (RZ, m, m, RZ))], '3eqtrd', '( Re ` %s ) = ( %s + %s )' % (zm, m, RZ))
    le = st([re, sy(w, a, zmc, 'releabs', '( Re ` %s ) <_ ( abs ` %s )' % (zm, zm))], 'eqbrtrrd', '( %s + %s ) <_ ( abs ` %s )' % (m, RZ, zm))
    ar = st([zmc], 'abscld', '( abs ` %s ) e. RR' % zm)
    mr = st([mn], 'nnred', '%s e. RR' % m)
    m1 = st([mn], 'nnge1d', '1 <_ %s' % m)
    gt = lin.linarith(w, a, [le, m1, x0], '0 < ( abs ` %s )' % zm, leaves={m: ('RR', mr), RZ: ('RR', xr), '( abs ` %s )' % zm: ('RR', ar)},
                      atoms=['( abs ` %s )' % zm, RZ])
    ne = st([gt, sy(w, a, zmc, 'absgt0', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (zm, zm))], 'mpbird', '%s =/= 0' % zm)
    return dict(xr=xr, mc=mc, zmc=zmc, le=le, ar=ar, gt=gt, ne=ne, mr=mr, zm=zm)


def z5deutb():
    w = W('z5deutb', "The Euler-product factor of Gamma ( set.mm's gamcvg2 ) at m has modulus at most ( m + Re z ) / | z + m | on the strip "
                     "0 <_ Re z <_ 1: its numerator has modulus ( ( m + 1 ) / m ) ^ Re z <_ 1 + Re z / m (Bernoulli, z5dbern).")
    a = '( ( Z e. CC /\\ %s ) /\\ M e. NN )' % STRIP
    st = mkst(w, a)
    zc = st([], 'simpll', 'Z e. CC'); mn = st([], 'simpr', 'M e. NN')
    x0 = st([st([], 'simplr', STRIP)], 'simpld', '0 <_ %s' % RZ); x1 = st([st([], 'simplr', STRIP)], 'simprd', '%s <_ 1' % RZ)
    f = zfacts(w, a, zc, x0, x1, 'M', mn, st)
    B = '( ( M + 1 ) / M )'
    mc = f['mc']; mne = st([mn], 'nnne0d', 'M =/= 0'); mrp = st([mn], 'nnrpd', 'M e. RR+')
    brp = st([st([st([mn], 'peano2nnd', '( M + 1 ) e. NN')], 'nnrpd', '( M + 1 ) e. RR+'), mrp], 'rpdivcld', '%s e. RR+' % B)
    # B = 1 + 1 / M
    b1 = st([mc, st([], '1cnd', '1 e. CC'), mc, mne], 'divdird', '%s = ( ( M / M ) + ( 1 / M ) )' % B)
    b2 = st([b1, st([st([mc, mne], 'dividd', '( M / M ) = 1')], 'oveq1d', '( ( M / M ) + ( 1 / M ) ) = ( 1 + ( 1 / M ) )')], 'eqtrd', '%s = ( 1 + ( 1 / M ) )' % B)
    im = st([mn], 'nnrecred', '( 1 / M ) e. RR')
    bm1 = st([st([b2], 'oveq1d', '( %s - 1 ) = ( ( 1 + ( 1 / M ) ) - 1 )' % B), st([st([], '1cnd', '1 e. CC'), st([im], 'recnd', '( 1 / M ) e. CC')], 'pncan2d',
                                                                                     '( ( 1 + ( 1 / M ) ) - 1 ) = ( 1 / M )')], 'eqtrd', '( %s - 1 ) = ( 1 / M )' % B)
    ilt = st([st([mrp], 'rpreccld', '( 1 / M ) e. RR+')], 'rpgt0d', '0 < ( 1 / M )')
    br = st([brp], 'rpred', '%s e. RR' % B)
    b1le = lin.linarith(w, a, [b2, ilt], '1 <_ %s' % B, leaves={B: ('RR', br), '( 1 / M )': ('RR', im)}, atoms=[B, '( 1 / M )'])
    xr = f['xr']
    bern = st([st([br, b1le], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (B, B)), st([xr, st([x0, x1], 'jca', '( 0 <_ %s /\\ %s <_ 1 )' % (RZ, RZ))], 'jca',
                                                                                  '( %s e. RR /\\ ( 0 <_ %s /\\ %s <_ 1 ) )' % (RZ, RZ, RZ)), w.inst('z5dbern')], 'syl2anc',
               '( %s ^c %s ) <_ ( 1 + ( %s x. ( %s - 1 ) ) )' % (B, RZ, RZ, B))
    # 1 + X ( B - 1 ) = ( M + X ) / M
    xc = st([xr], 'recnd', '%s e. CC' % RZ)
    e1 = st([st([bm1], 'oveq2d', '( %s x. ( %s - 1 ) ) = ( %s x. ( 1 / M ) )' % (RZ, B, RZ)), st([st([xc, mc, mne], 'divrecd', '( %s / M ) = ( %s x. ( 1 / M ) )' % (RZ, RZ))], 'eqcomd',
                                                                                             '( %s x. ( 1 / M ) ) = ( %s / M )' % (RZ, RZ))], 'eqtrd', '( %s x. ( %s - 1 ) ) = ( %s / M )' % (RZ, B, RZ))
    e2 = st([mc, xc, mc, mne], 'divdird', '( ( M + %s ) / M ) = ( ( M / M ) + ( %s / M ) )' % (RZ, RZ))
    e3 = st([e2, st([st([mc, mne], 'dividd', '( M / M ) = 1')], 'oveq1d', '( ( M / M ) + ( %s / M ) ) = ( 1 + ( %s / M ) )' % (RZ, RZ))], 'eqtrd',
            '( ( M + %s ) / M ) = ( 1 + ( %s / M ) )' % (RZ, RZ))
    e4 = st([st([e1], 'oveq2d', '( 1 + ( %s x. ( %s - 1 ) ) ) = ( 1 + ( %s / M ) )' % (RZ, B, RZ)), e3], 'eqtr4d', '( 1 + ( %s x. ( %s - 1 ) ) ) = ( ( M + %s ) / M )' % (RZ, B, RZ))
    bern2 = st([bern, e4], 'breqtrd', '( %s ^c %s ) <_ ( ( M + %s ) / M )' % (B, RZ, RZ))
    # the modulus of the factor
    NUMER = '( %s ^c Z )' % B
    DEN = '( ( Z / M ) + 1 )'
    zm = f['zm']
    d1 = st([zc, mc, mc, mne], 'divdird', '( %s / M ) = ( ( Z / M ) + ( M / M ) )' % zm)
    d2 = st([d1, st([st([mc, mne], 'dividd', '( M / M ) = 1')], 'oveq2d', '( ( Z / M ) + ( M / M ) ) = %s' % DEN)], 'eqtrd', '( %s / M ) = %s' % (zm, DEN))
    dne = st([d2, st([f['zmc'], mc, f['ne'], mne], 'divne0d', '( %s / M ) =/= 0' % zm)], 'eqnetrrd', '%s =/= 0' % DEN)
    dc = st([d2, st([f['zmc'], mc, mne], 'divcld', '( %s / M ) e. CC' % zm)], 'eqeltrrd', '%s e. CC' % DEN)
    ncc = st([st([brp], 'rpcnd', '%s e. CC' % B), zc], 'cxpcld', '%s e. CC' % NUMER)
    ad = st([ncc, dc, dne], 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (NUMER, DEN, NUMER, DEN))
    an = st([brp, zc, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( %s ^c %s )' % (NUMER, B, RZ))
    ad2 = st([st([d2], 'eqcomd', '%s = ( %s / M )' % (DEN, zm))], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s / M ) )' % (DEN, zm))
    ad3 = st([f['zmc'], mc, mne], 'absdivd', '( abs ` ( %s / M ) ) = ( ( abs ` %s ) / ( abs ` M ) )' % (zm, zm))
    am = st([f['mr'], st([mrp], 'rpge0d', '0 <_ M')], 'absidd', '( abs ` M ) = M')
    AZ = '( abs ` %s )' % zm
    ad4 = st([ad2, ad3, st([am], 'oveq2d', '( %s / ( abs ` M ) ) = ( %s / M )' % (AZ, AZ))], '3eqtrd', '( abs ` %s ) = ( %s / M )' % (DEN, AZ))
    val = st([ad, st([an, ad4], 'oveq12d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( %s ^c %s ) / ( %s / M ) )' % (NUMER, DEN, B, RZ, AZ))], 'eqtrd',
             '( abs ` %s ) = ( ( %s ^c %s ) / ( %s / M ) )' % (EUTM('M'), B, RZ, AZ))
    azrp = st([f['ar'], f['gt']], 'elrpd', '%s e. RR+' % AZ)
    azm = st([azrp, mrp], 'rpdivcld', '( %s / M ) e. RR+' % AZ)
    bxr = st([st([brp, xr], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (B, RZ))], 'rpred', '( %s ^c %s ) e. RR' % (B, RZ))
    mxr = st([st([f['mr'], xr], 'readdcld', '( M + %s ) e. RR' % RZ), mrp], 'rerpdivcld', '( ( M + %s ) / M ) e. RR' % RZ)
    le = st([bxr, mxr, azm, bern2], 'lediv1dd', '( ( %s ^c %s ) / ( %s / M ) ) <_ ( ( ( M + %s ) / M ) / ( %s / M ) )' % (B, RZ, AZ, RZ, AZ))
    c7 = st([st([st([f['mr'], xr], 'readdcld', '( M + %s ) e. RR' % RZ)], 'recnd', '( M + %s ) e. CC' % RZ), st([azrp], 'rpcnd', '%s e. CC' % AZ), mc,
             st([azrp], 'rpne0d', '%s =/= 0' % AZ), mne], 'divcan7d', '( ( ( M + %s ) / M ) / ( %s / M ) ) = ( ( M + %s ) / %s )' % (RZ, AZ, RZ, AZ))
    le2 = st([le, c7], 'breqtrd', '( ( %s ^c %s ) / ( %s / M ) ) <_ ( ( M + %s ) / %s )' % (B, RZ, AZ, RZ, AZ))
    w.qed([val, le2], 'eqbrtrd', STATEMENTS['z5deutb'])
    return w


def ratfacts(w, ante, zc, x0, x1, kst, k='k'):
    """under ante with kst: ( ante -> k e. NN ): RAT(k) real, >= 0, <= 1"""
    st = mkst(w, ante)
    f = zfacts(w, ante, zc, x0, x1, k, kst, st)
    AZ = '( abs ` %s )' % f['zm']
    azrp = st([f['ar'], f['gt']], 'elrpd', '%s e. RR+' % AZ)
    num_ = '( %s + %s )' % (k, RZ)
    nr = st([f['mr'], f['xr']], 'readdcld', '%s e. RR' % num_)
    n0 = lin.linarith(w, ante, [st([kst], 'nnge1d', '1 <_ %s' % k), x0], '0 <_ %s' % num_, leaves={k: ('RR', f['mr']), RZ: ('RR', f['xr'])}, atoms=[RZ])
    rr = st([nr, azrp], 'rerpdivcld', '%s e. RR' % RAT(k))
    r0 = st([nr, azrp, n0], 'divge0d', '0 <_ %s' % RAT(k))
    r1 = st([f['le'], st([nr, azrp, w.inst('divle1le')], 'syl2anc', '( %s <_ 1 <-> %s <_ %s )' % (RAT(k), num_, AZ))], 'mpbird', '%s <_ 1' % RAT(k))
    return dict(rr=rr, r0=r0, r1=r1)


def z5dgzp():
    w = W('z5dgzp', "The modulus of Gamma ( z ) z is at most the product of the first M ratios ( m + Re z ) / | z + m |, for every M, on the "
                    "strip 0 <_ Re z <_ 1: every Euler factor of set.mm's gamcvg2 has modulus at most its ratio (z5deutb), every ratio "
                    "is at most 1, and the partial products converge (climabs, climle).")
    a = '( ( Z e. ( CC \\ ( ZZ \\ NN ) ) /\\ %s ) /\\ M e. NN0 )' % STRIP
    st = mkst(w, a)
    zd = st([], 'simpll', 'Z e. ( CC \\ ( ZZ \\ NN ) )')
    zc = sy(w, a, zd, 'eldifi', 'Z e. CC')
    x0 = st([st([], 'simplr', STRIP)], 'simpld', '0 <_ %s' % RZ); x1 = st([st([], 'simplr', STRIP)], 'simprd', '%s <_ 1' % RZ)
    mn0 = st([], 'simpr', 'M e. NN0')
    F = '( j e. NN |-> %s )' % EUTM('j')
    SEQ = 'seq 1 ( x. , %s )' % F
    GZ = '( ( _G ` Z ) x. Z )'
    gam = w.s([w.s([], 'eqid', '%s = %s' % (F, F)), zd], 'gamcvg2', '( %s -> %s ~~> %s )' % (a, SEQ, GZ))
    G = '( i e. NN |-> ( abs ` ( %s ` i ) ) )' % SEQ
    nuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = st([], '1zzd', '1 e. ZZ')
    gex = st([a1(w, a, w.s([], 'nnex', 'NN e. _V'), 'NN e. _V')], 'mptexd', '%s e. _V' % G)
    an = '( %s /\\ n e. NN )' % a
    sn = mkst(w, an)
    nn_ = sn([], 'simpr', 'n e. NN')
    # the partial products: seq ` n = prod ( 1 ... n ) EUT
    def seqval(ante, nst):
        s_ = mkst(w, ante)
        ak = '( %s /\\ k e. ( 1 ... n ) )' % ante
        sk = mkst(w, ak)
        kn = sy(w, ak, sk([], 'simpr', 'k e. ( 1 ... n )'), 'elfznn', 'k e. NN')
        fv, _ = mpv(w, ak, 'j', 'NN', EUTM('j'), 'k', kn)
        zck = lift(w, zc, ak)
        B = '( ( k + 1 ) / k )'
        brp = sk([sk([sk([kn], 'peano2nnd', '( k + 1 ) e. NN')], 'nnrpd', '( k + 1 ) e. RR+'), sk([kn], 'nnrpd', 'k e. RR+')], 'rpdivcld', '%s e. RR+' % B)
        numc = sk([sk([brp], 'rpcnd', '%s e. CC' % B), zck], 'cxpcld', '( %s ^c Z ) e. CC' % B)
        kc = sk([kn], 'nncnd', 'k e. CC'); kne = sk([kn], 'nnne0d', 'k =/= 0')
        # the denominator is nonzero: ( Z / k ) + 1 = ( Z + k ) / k
        f_ = zfacts(w, ak, zck, lift(w, x0, ak), lift(w, x1, ak), 'k', kn, sk)
        d1 = sk([zck, kc, kc, kne], 'divdird', '( ( Z + k ) / k ) = ( ( Z / k ) + ( k / k ) )')
        d2 = sk([d1, sk([sk([kc, kne], 'dividd', '( k / k ) = 1')], 'oveq2d', '( ( Z / k ) + ( k / k ) ) = ( ( Z / k ) + 1 )')], 'eqtrd', '( ( Z + k ) / k ) = ( ( Z / k ) + 1 )')
        dne = sk([d2, sk([f_['zmc'], kc, f_['ne'], kne], 'divne0d', '( ( Z + k ) / k ) =/= 0')], 'eqnetrrd', '( ( Z / k ) + 1 ) =/= 0')
        dcc = sk([d2, sk([f_['zmc'], kc, kne], 'divcld', '( ( Z + k ) / k ) e. CC')], 'eqeltrrd', '( ( Z / k ) + 1 ) e. CC')
        ec = sk([numc, dcc, dne], 'divcld', '%s e. CC' % EUTM('k'))
        nuz1 = s_([nst, w.s([], 'elnnuz', '( n e. NN <-> n e. ( ZZ>= ` 1 ) )')], 'sylib', 'n e. ( ZZ>= ` 1 )')
        return s_([fv, nuz1, ec], 'fprodser', 'prod_ k e. ( 1 ... n ) %s = ( %s ` n )' % (EUTM('k'), SEQ)), ec, ak
    sv, ec, ak = seqval(an, nn_)
    fin1n = sn([], 'fzfid', '( 1 ... n ) e. Fin')
    sc = sn([fin1n, ec], 'fprodcl', 'prod_ k e. ( 1 ... n ) %s e. CC' % EUTM('k'))
    seqc = sn([sv, sc], 'eqeltrrd', '( %s ` n ) e. CC' % SEQ)
    gv, _ = mpv(w, an, 'i', 'NN', '( abs ` ( %s ` i ) )' % SEQ, 'n', nn_)
    ab = w.s([nuz, gam, gex, one, seqc, gv], 'climabs', '( %s -> %s ~~> ( abs ` %s ) )' % (a, G, GZ))
    # the constant sequence
    P = 'prod_ k e. ( 1 ... M ) %s' % RAT('k')
    UZ = '( ZZ>= ` ( M + 1 ) )'
    H = '( %s X. { %s } )' % (UZ, P)
    am_ = '( %s /\\ k e. ( 1 ... M ) )' % a
    smk = mkst(w, am_)
    kmn = sy(w, am_, smk([], 'simpr', 'k e. ( 1 ... M )'), 'elfznn', 'k e. NN')
    rfm = ratfacts(w, am_, lift(w, zc, am_), lift(w, x0, am_), lift(w, x1, am_), kmn)
    fin1m = st([], 'fzfid', '( 1 ... M ) e. Fin')
    pr = st([fin1m, rfm['rr']], 'fprodrecl', '%s e. RR' % P)
    nf = w.s([], 'nfv', 'F/ k %s' % a)
    p0 = w.s([nf, fin1m, rfm['rr'], rfm['r0']], 'fprodge0', '( %s -> 0 <_ %s )' % (a, P))
    m1n = sy(w, a, mn0, 'nn0p1nn', '( M + 1 ) e. NN')
    m1z = st([m1n], 'nnzd', '( M + 1 ) e. ZZ')
    hex_ = st([st([], 'fvexd', '%s e. _V' % UZ), a1(w, a, w.s([], 'snex', '{ %s } e. _V' % P), '{ %s } e. _V' % P), w.inst('xpexg')], 'syl2anc', '%s e. _V' % H)
    au = '( %s /\\ n e. %s )' % (a, UZ)
    su = mkst(w, au)
    hv = su([su([lift(w, pr, au), su([], 'simpr', 'n e. %s' % UZ)], 'jca', '( %s e. RR /\\ n e. %s )' % (P, UZ)), w.inst('fvconst2g')], 'syl', '( %s ` n ) = %s' % (H, P))
    uzd = w.s([], 'eqid', '%s = %s' % (UZ, UZ))
    hc = w.s([uzd, m1z, hex_, st([pr], 'recnd', '%s e. CC' % P), hv], 'climconst', '( %s -> %s ~~> %s )' % (a, H, P))
    # per n >= M + 1
    nu = sy(w, au, su([lift(w, m1n, au), su([], 'simpr', 'n e. %s' % UZ)], 'jca', '( ( M + 1 ) e. NN /\\ n e. %s )' % UZ), 'eluznn', 'n e. NN')
    sv2, ec2, ak2 = seqval(au, nu)
    gv2, _ = mpv(w, au, 'i', 'NN', '( abs ` ( %s ` i ) )' % SEQ, 'n', nu)
    fin2 = su([], 'fzfid', '( 1 ... n ) e. Fin')
    PE = 'prod_ k e. ( 1 ... n ) %s' % EUTM('k')
    abp = su([fin2, ec2], 'z5fprodabs', '( abs ` %s ) = prod_ k e. ( 1 ... n ) ( abs ` %s )' % (PE, EUTM('k')))
    s2 = mkst(w, ak2)
    kn2 = sy(w, ak2, s2([], 'simpr', 'k e. ( 1 ... n )'), 'elfznn', 'k e. NN')
    zc2 = lift(w, zc, ak2); x02 = lift(w, x0, ak2); x12 = lift(w, x1, ak2)
    eb = s2([s2([s2([zc2, s2([x02, x12], 'jca', STRIP)], 'jca', '( Z e. CC /\\ %s )' % STRIP), kn2], 'jca', '( ( Z e. CC /\\ %s ) /\\ k e. NN )' % STRIP), w.inst('z5deutb')],
            'syl', '( abs ` %s ) <_ %s' % (EUTM('k'), RAT('k')))
    rf2 = ratfacts(w, ak2, zc2, x02, x12, kn2)
    nf2 = w.s([], 'nfv', 'F/ k %s' % au)
    le1 = w.s([nf2, fin2, s2([ec2], 'abscld', '( abs ` %s ) e. RR' % EUTM('k')), s2([ec2], 'absge0d', '0 <_ ( abs ` %s )' % EUTM('k')), rf2['rr'], eb], 'fprodle',
              '( %s -> prod_ k e. ( 1 ... n ) ( abs ` %s ) <_ prod_ k e. ( 1 ... n ) %s )' % (au, EUTM('k'), RAT('k')))
    # split ( 1 ... n ) at M
    mz = su([lift(w, mn0, au)], 'nn0zd', 'M e. ZZ')
    m1u = su([lift(w, m1n, au), w.s([], 'elnnuz', '( ( M + 1 ) e. NN <-> ( M + 1 ) e. ( ZZ>= ` 1 ) )')], 'sylib', '( M + 1 ) e. ( ZZ>= ` 1 )')
    nM = su([mz, su([], 'simpr', 'n e. %s' % UZ), w.inst('peano2uzr')], 'syl2anc', 'n e. ( ZZ>= ` M )')
    spl = su([su([m1u, nM], 'jca', '( ( M + 1 ) e. ( ZZ>= ` 1 ) /\\ n e. ( ZZ>= ` M ) )'), w.inst('fzsplit2')], 'syl', '( 1 ... n ) = ( ( 1 ... M ) u. ( ( M + 1 ) ... n ) )')
    dj = su([su([su([lift(w, mn0, au)], 'nn0red', 'M e. RR')], 'ltp1d', 'M < ( M + 1 )'), w.inst('fzdisj')], 'syl', '( ( 1 ... M ) i^i ( ( M + 1 ) ... n ) ) = (/)')
    ak3 = '( %s /\\ k e. ( 1 ... n ) )' % au
    RC = s2([rf2['rr']], 'recnd', '%s e. CC' % RAT('k'))
    splp = su([dj, spl, fin2, RC], 'fprodsplit', 'prod_ k e. ( 1 ... n ) %s = ( %s x. prod_ k e. ( ( M + 1 ) ... n ) %s )' % (RAT('k'), P, RAT('k')))
    # the tail product is at most 1
    at_ = '( %s /\\ k e. ( ( M + 1 ) ... n ) )' % au
    stt = mkst(w, at_)
    ktn = stt([stt([lift(w, m1n, at_), sy(w, at_, stt([], 'simpr', 'k e. ( ( M + 1 ) ... n )'), 'elfzuz', 'k e. ( ZZ>= ` ( M + 1 ) )')], 'jca',
                   '( ( M + 1 ) e. NN /\\ k e. ( ZZ>= ` ( M + 1 ) ) )'), w.inst('eluznn')], 'syl', 'k e. NN')
    rft = ratfacts(w, at_, lift(w, zc, at_), lift(w, x0, at_), lift(w, x1, at_), ktn)
    fint = su([], 'fzfid', '( ( M + 1 ) ... n ) e. Fin')
    PT = 'prod_ k e. ( ( M + 1 ) ... n ) %s' % RAT('k')
    tle = w.s([nf2, fint, rft['rr'], rft['r0'], stt([], '1red', '1 e. RR'), rft['r1']], 'fprodle', '( %s -> %s <_ prod_ k e. ( ( M + 1 ) ... n ) 1 )' % (au, PT))
    t1 = su([su([fint], 'olcd', '( ( ( M + 1 ) ... n ) C_ ( ZZ>= ` 1 ) \\/ ( ( M + 1 ) ... n ) e. Fin )'), w.inst('prod1')], 'syl', 'prod_ k e. ( ( M + 1 ) ... n ) 1 = 1')
    tle1 = su([tle, t1], 'breqtrd', '%s <_ 1' % PT)
    ptr = su([fint, rft['rr']], 'fprodrecl', '%s e. RR' % PT)
    pru = lift(w, pr, au); p0u = lift(w, p0, au)
    m_ = su([ptr, su([], '1red', '1 e. RR'), pru, p0u, tle1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 1 )' % (P, PT, P))
    m2 = su([m_, su([su([pru], 'recnd', '%s e. CC' % P)], 'mulridd', '( %s x. 1 ) = %s' % (P, P))], 'breqtrd', '( %s x. %s ) <_ %s' % (P, PT, P))
    # chain: G ` n = | seq ` n | = | prod | = prod | . | <_ prod RAT = P x. PT <_ P = H ` n
    e1 = su([gv2, su([su([sv2], 'eqcomd', '( %s ` n ) = %s' % (SEQ, PE))], 'fveq2d', '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (SEQ, PE))], 'eqtrd',
            '( %s ` n ) = ( abs ` %s )' % (G, PE))
    e2 = su([e1, abp], 'eqtrd', '( %s ` n ) = prod_ k e. ( 1 ... n ) ( abs ` %s )' % (G, EUTM('k')))
    lhsle = su([e2, le1], 'eqbrtrd', '( %s ` n ) <_ prod_ k e. ( 1 ... n ) %s' % (G, RAT('k')))
    lhsle2 = su([lhsle, splp], 'breqtrd', '( %s ` n ) <_ ( %s x. %s )' % (G, P, PT))
    gnr = su([e2, su([fin2, s2([ec2], 'abscld', '( abs ` %s ) e. RR' % EUTM('k'))], 'fprodrecl', 'prod_ k e. ( 1 ... n ) ( abs ` %s ) e. RR' % EUTM('k'))], 'eqeltrd',
             '( %s ` n ) e. RR' % G)
    bnd = su([gnr, su([pru, ptr], 'remulcld', '( %s x. %s ) e. RR' % (P, PT)), pru, lhsle2, m2], 'letrd', '( %s ` n ) <_ %s' % (G, P))
    bnd2 = su([bnd, su([hv], 'eqcomd', '%s = ( %s ` n )' % (P, H))], 'breqtrd', '( %s ` n ) <_ ( %s ` n )' % (G, H))
    hr = su([hv, pru], 'eqeltrd', '( %s ` n ) e. RR' % H)
    w.qed([uzd, m1z, ab, hc, gnr, hr, bnd2], 'climle', STATEMENTS['z5dgzp'])
    return w


def z5dfac():
    w = W('z5dfac', "The squared Euler ratio ( ( m + Re z ) / | z + m | ) ^ 2 is at most 2 ( ( m + 1 ) / ( m + 1 + n ) ) ^ 2 when n <_ | Im z |: "
                    "with a = m + Re z <_ b = m + 1, u = | Im z | and q = b / ( b + n ): a <_ q ( a + n ) <_ q ( a + u ) and "
                    "( a + u ) ^ 2 <_ 2 ( a ^ 2 + u ^ 2 ).")
    a = '( ( Z e. CC /\\ %s ) /\\ ( N e. NN0 /\\ N <_ %s ) /\\ M e. NN )' % (STRIP, AIZ)
    st = mkst(w, a)
    zc = st([st([], 'simp1', '( Z e. CC /\\ %s )' % STRIP)], 'simpld', 'Z e. CC')
    sp = st([st([], 'simp1', '( Z e. CC /\\ %s )' % STRIP)], 'simprd', STRIP)
    x0 = st([sp], 'simpld', '0 <_ %s' % RZ); x1 = st([sp], 'simprd', '%s <_ 1' % RZ)
    nn0 = st([st([], 'simp2', '( N e. NN0 /\\ N <_ %s )' % AIZ)], 'simpld', 'N e. NN0')
    nu = st([st([], 'simp2', '( N e. NN0 /\\ N <_ %s )' % AIZ)], 'simprd', 'N <_ %s' % AIZ)
    mn = st([], 'simp3', 'M e. NN')
    f = zfacts(w, a, zc, x0, x1, 'M', mn, st)
    A_ = '( M + %s )' % RZ; B_ = '( M + 1 )'; Y = '( Im ` Z )'; U = AIZ
    zm = f['zm']; AZ = '( abs ` %s )' % zm
    # | Z + M | ^ 2 = a ^ 2 + Y ^ 2
    im1 = st([zc, f['mc'], w.inst('imadd')], 'syl2anc', '( Im ` %s ) = ( %s + ( Im ` M ) )' % (zm, Y))
    im2 = sy(w, a, f['mr'], 'reim0', '( Im ` M ) = 0')
    yr = st([zc], 'imcld', '%s e. RR' % Y)
    im3 = st([im1, st([im2], 'oveq2d', '( %s + ( Im ` M ) ) = ( %s + 0 )' % (Y, Y)), st([st([yr], 'recnd', '%s e. CC' % Y)], 'addridd', '( %s + 0 ) = %s' % (Y, Y))], '3eqtrd',
              '( Im ` %s ) = %s' % (zm, Y))
    reeq = st([zc, f['mc'], w.inst('readd')], 'syl2anc', '( Re ` %s ) = ( %s + ( Re ` M ) )' % (zm, RZ))
    sq = sy(w, a, f['zmc'], 'absvalsq2', '( %s ^ 2 ) = ( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (AZ, zm, zm))
    ReZM = '( Re ` %s )' % zm
    # Re ( Z + M ) = M + Re Z: from zfacts' le proof we recompute
    re2 = sy(w, a, f['mr'], 'rere', '( Re ` M ) = M')
    reA = st([reeq, st([re2], 'oveq2d', '( %s + ( Re ` M ) ) = ( %s + M )' % (RZ, RZ)), st([st([f['xr']], 'recnd', '%s e. CC' % RZ), f['mc']], 'addcomd', '( %s + M ) = %s' % (RZ, A_))],
             '3eqtrd', '%s = %s' % (ReZM, A_))
    rw, new = w.rewrite('( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (zm, zm), {ReZM: (A_, reA), '( Im ` %s )' % zm: (Y, im3)}, a)
    d1 = st([sq, rw], 'eqtrd', '( %s ^ 2 ) = %s' % (AZ, new))
    yu = sy(w, a, yr, 'absresq', '( %s ^ 2 ) = ( %s ^ 2 )' % (U, Y))
    # q
    Q = QK('M')
    nr = st([nn0], 'nn0red', 'N e. RR'); n0 = st([nn0], 'nn0ge0d', '0 <_ N')
    br = st([f['mr'], st([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % B_)
    bnr = st([br, nr], 'readdcld', '( %s + N ) e. RR' % B_)
    bp = lin.linarith(w, a, [st([mn], 'nnge1d', '1 <_ M')], '0 < %s' % B_, leaves={'M': ('RR', f['mr'])})
    bnp = lin.linarith(w, a, [st([mn], 'nnge1d', '1 <_ M'), n0], '0 < ( %s + N )' % B_, leaves={'M': ('RR', f['mr']), 'N': ('RR', nr)})
    bnrp = st([bnr, bnp], 'elrpd', '( %s + N ) e. RR+' % B_)
    qr = st([br, bnrp], 'rerpdivcld', '%s e. RR' % Q)
    q0 = st([br, bnrp, st([bp], 'ltled', '0 <_ %s' % B_)], 'divge0d', '0 <_ %s' % Q)
    qle = st([lin.linarith(w, a, [n0], '%s <_ ( %s + N )' % (B_, B_), leaves={'M': ('RR', f['mr']), 'N': ('RR', nr)}),
              st([br, bnrp, w.inst('divle1le')], 'syl2anc', '( %s <_ 1 <-> %s <_ ( %s + N ) )' % (Q, B_, B_))], 'mpbird', '%s <_ 1' % Q)
    qb = st([st([br], 'recnd', '%s e. CC' % B_), st([bnr], 'recnd', '( %s + N ) e. CC' % B_), st([bnrp], 'rpne0d', '( %s + N ) =/= 0' % B_)], 'divcan1d',
            '( %s x. ( %s + N ) ) = %s' % (Q, B_, B_))
    ar = st([f['mr'], f['xr']], 'readdcld', '%s e. RR' % A_)
    a0 = lin.linarith(w, a, [st([mn], 'nnge1d', '1 <_ M'), x0], '0 <_ %s' % A_, leaves={'M': ('RR', f['mr']), RZ: ('RR', f['xr'])}, atoms=[RZ])
    ab = lin.linarith(w, a, [x1], '%s <_ %s' % (A_, B_), leaves={'M': ('RR', f['mr']), RZ: ('RR', f['xr'])}, atoms=[RZ])
    ur = st([st([yr], 'recnd', '%s e. CC' % Y)], 'abscld', '%s e. RR' % U)
    cl = Closure(w, a, {Q: ('RR', qr), RZ: ('RR', f['xr']), 'M': ('RR', f['mr']), 'N': ('RR', nr), U: ('RR', ur), Y: ('RR', yr)})
    for x in (Q, RZ, U, Y):
        cl.atom(x)
    pr = st([st([st([], '1red', '1 e. RR'), qr], 'resubcld', '( 1 - %s ) e. RR' % Q), st([br, ar], 'resubcld', '( %s - %s ) e. RR' % (B_, A_)),
             lin.linarith(w, a, [qle], '0 <_ ( 1 - %s )' % Q, closure=cl), lin.linarith(w, a, [ab], '0 <_ ( %s - %s )' % (B_, A_), closure=cl)], 'mulge0d',
            '0 <_ ( ( 1 - %s ) x. ( %s - %s ) )' % (Q, B_, A_))
    s2 = lin.linarith(w, a, [pr, qb], '%s <_ ( %s x. ( %s + N ) )' % (A_, Q, A_), closure=cl, products=True)
    qan = st([qr, st([ar, nr], 'readdcld', '( %s + N ) e. RR' % A_)], 'remulcld', '( %s x. ( %s + N ) ) e. RR' % (Q, A_))
    s3 = st([st([ar, a0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (A_, A_)), st([qan, s2], 'jca', '( ( %s x. ( %s + N ) ) e. RR /\\ %s <_ ( %s x. ( %s + N ) ) )' % (Q, A_, A_, Q, A_)),
             w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( ( %s x. ( %s + N ) ) ^ 2 )' % (A_, Q, A_))
    qan0 = st([qr, st([ar, nr], 'readdcld', '( %s + N ) e. RR' % A_), q0,
               lin.linarith(w, a, [a0, n0], '0 <_ ( %s + N )' % A_, closure=cl)], 'mulge0d', '0 <_ ( %s x. ( %s + N ) )' % (Q, A_))
    s4a = st([st([ar, nr], 'readdcld', '( %s + N ) e. RR' % A_), st([ar, ur], 'readdcld', '( %s + %s ) e. RR' % (A_, U)), qr, q0,
              lin.linarith(w, a, [nu], '( %s + N ) <_ ( %s + %s )' % (A_, A_, U), closure=cl)], 'lemul2ad', '( %s x. ( %s + N ) ) <_ ( %s x. ( %s + %s ) )' % (Q, A_, Q, A_, U))
    qau = st([qr, st([ar, ur], 'readdcld', '( %s + %s ) e. RR' % (A_, U))], 'remulcld', '( %s x. ( %s + %s ) ) e. RR' % (Q, A_, U))
    s4 = st([st([qan, qan0], 'jca', '( ( %s x. ( %s + N ) ) e. RR /\\ 0 <_ ( %s x. ( %s + N ) ) )' % (Q, A_, Q, A_)),
             st([qau, s4a], 'jca', '( ( %s x. ( %s + %s ) ) e. RR /\\ ( %s x. ( %s + N ) ) <_ ( %s x. ( %s + %s ) ) )' % (Q, A_, U, Q, A_, Q, A_, U)), w.inst('le2sq2')],
            'syl2anc', '( ( %s x. ( %s + N ) ) ^ 2 ) <_ ( ( %s x. ( %s + %s ) ) ^ 2 )' % (Q, A_, Q, A_, U))
    S_ = '( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (A_, U)
    q2 = '( %s ^ 2 )' % Q
    sg = st([st([ar, ur], 'resubcld', '( %s - %s ) e. RR' % (A_, U))], 'sqge0d', '0 <_ ( ( %s - %s ) ^ 2 )' % (A_, U))
    cla = Closure(w, a, {A_: ('RR', ar), U: ('RR', ur)})
    cla.atom(A_); cla.atom(U)
    au2 = lin.linarith(w, a, [sg], '( ( %s + %s ) ^ 2 ) <_ ( 2 x. %s )' % (A_, U, S_), closure=cla, products=True)
    q2r = st([qr], 'resqcld', '%s e. RR' % q2); q20 = st([qr], 'sqge0d', '0 <_ %s' % q2)
    aur = st([ar, ur], 'readdcld', '( %s + %s ) e. RR' % (A_, U))
    sr_ = st([st([ar], 'resqcld', '( %s ^ 2 ) e. RR' % A_), st([ur], 'resqcld', '( %s ^ 2 ) e. RR' % U)], 'readdcld', '%s e. RR' % S_)
    s5 = st([st([aur], 'resqcld', '( ( %s + %s ) ^ 2 ) e. RR' % (A_, U)), st([litr(w, a, '2'), sr_], 'remulcld', '( 2 x. %s ) e. RR' % S_), q2r, q20, au2], 'lemul2ad',
            '( %s x. ( ( %s + %s ) ^ 2 ) ) <_ ( %s x. ( 2 x. %s ) )' % (q2, A_, U, q2, S_))
    sqm = st([st([qr], 'recnd', '%s e. CC' % Q), st([aur], 'recnd', '( %s + %s ) e. CC' % (A_, U))], 'sqmuld', '( ( %s x. ( %s + %s ) ) ^ 2 ) = ( %s x. ( ( %s + %s ) ^ 2 ) )' % (Q, A_, U, q2, A_, U))
    s5b = st([sqm, s5], 'eqbrtrd', '( ( %s x. ( %s + %s ) ) ^ 2 ) <_ ( %s x. ( 2 x. %s ) )' % (Q, A_, U, q2, S_))
    GOALR = '( ( %s ^ 2 ) x. ( 2 x. ( %s ^ 2 ) ) )' % (AZ, Q)
    d1u = st([d1, st([yu], 'oveq2d', '( ( %s ^ 2 ) + ( %s ^ 2 ) ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (A_, U, A_, Y))], 'eqtr4d', '( %s ^ 2 ) = %s' % (AZ, S_))
    q2c = st([q2r], 'recnd', '%s e. CC' % q2); sc_ = st([sr_], 'recnd', '%s e. CC' % S_)
    m12 = st([q2c, st([], '2cnd', '2 e. CC'), sc_], 'mul12d', '( %s x. ( 2 x. %s ) ) = ( 2 x. ( %s x. %s ) )' % (q2, S_, q2, S_))
    m12b = st([sc_, st([], '2cnd', '2 e. CC'), q2c], 'mul12d', '( %s x. ( 2 x. %s ) ) = ( 2 x. ( %s x. %s ) )' % (S_, q2, S_, q2))
    mc_ = st([st([q2c, sc_], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (q2, S_, S_, q2))], 'oveq2d', '( 2 x. ( %s x. %s ) ) = ( 2 x. ( %s x. %s ) )' % (q2, S_, S_, q2))
    rr_ = st([m12, mc_, st([m12b], 'eqcomd', '( 2 x. ( %s x. %s ) ) = ( %s x. ( 2 x. %s ) )' % (S_, q2, S_, q2))], '3eqtrd',
             '( %s x. ( 2 x. %s ) ) = ( %s x. ( 2 x. %s ) )' % (q2, S_, S_, q2))
    rr2 = st([rr_, st([d1u], 'oveq1d', '%s = ( %s x. ( 2 x. %s ) )' % (GOALR, S_, q2))], 'eqtr4d', '( %s x. ( 2 x. %s ) ) = %s' % (q2, S_, GOALR))
    fin = st([st([ar], 'resqcld', '( %s ^ 2 ) e. RR' % A_), st([qan], 'resqcld', '( ( %s x. ( %s + N ) ) ^ 2 ) e. RR' % (Q, A_)),
              st([qau], 'resqcld', '( ( %s x. ( %s + %s ) ) ^ 2 ) e. RR' % (Q, A_, U)), s3, s4], 'letrd', '( %s ^ 2 ) <_ ( ( %s x. ( %s + %s ) ) ^ 2 )' % (A_, Q, A_, U))
    fin = st([st([ar], 'resqcld', '( %s ^ 2 ) e. RR' % A_), st([qau], 'resqcld', '( ( %s x. ( %s + %s ) ) ^ 2 ) e. RR' % (Q, A_, U)),
            st([st([f['ar']], 'resqcld', '( %s ^ 2 ) e. RR' % AZ), st([litr(w, a, '2'), q2r], 'remulcld', '( 2 x. %s ) e. RR' % q2)], 'remulcld', '%s e. RR' % GOALR),
            fin, st([s5b, rr2], 'breqtrd', '( ( %s x. ( %s + %s ) ) ^ 2 ) <_ %s' % (Q, A_, U, GOALR))], 'letrd', '( %s ^ 2 ) <_ %s' % (A_, GOALR))
    # divide
    azrp = st([f['ar'], f['gt']], 'elrpd', '%s e. RR+' % AZ)
    az2 = st([azrp, a1(w, a, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % AZ)
    tq = st([litr(w, a, '2'), st([qr], 'resqcld', '( %s ^ 2 ) e. RR' % Q)], 'remulcld', '( 2 x. ( %s ^ 2 ) ) e. RR' % Q)
    lm = st([fin, st([st([ar], 'resqcld', '( %s ^ 2 ) e. RR' % A_), tq, az2], 'ledivmuld', '( ( ( %s ^ 2 ) / ( %s ^ 2 ) ) <_ ( 2 x. ( %s ^ 2 ) ) <-> ( %s ^ 2 ) <_ %s )'
                                                                                           % (A_, AZ, Q, A_, GOALR))], 'mpbird', '( ( %s ^ 2 ) / ( %s ^ 2 ) ) <_ ( 2 x. ( %s ^ 2 ) )' % (A_, AZ, Q))
    sd = st([st([ar], 'recnd', '%s e. CC' % A_), st([azrp], 'rpcnd', '%s e. CC' % AZ), st([azrp], 'rpne0d', '%s =/= 0' % AZ)], 'sqdivd',
            '( %s ^ 2 ) = ( ( %s ^ 2 ) / ( %s ^ 2 ) )' % (RAT('M'), A_, AZ))
    w.qed([sd, lm], 'eqbrtrd', STATEMENTS['z5dfac'])
    return w


def z5dqnid():
    w = W('z5dqnid', "prod_ ( k = 1 .. n ) ( k + 1 ) / ( k + 1 + n ) = ( n + 1 ) / C ( 2 n + 1 , n ): numerator and denominator are the "
                     "falling factorials ( n + 1 ) FallFac n and ( 2 n + 1 ) FallFac n (fprodshft, fallfacval3), and bcfallfac turns "
                     "their quotient into C ( n + 1 , n ) / C ( 2 n + 1 , n ).")
    a = 'N e. NN0'
    st = mkst(w, a)
    nn0 = st([], 'id', a)
    nz = st([nn0], 'nn0zd', 'N e. ZZ'); nr = st([nn0], 'nn0red', 'N e. RR')
    FZ = '( 1 ... N )'
    fin = st([], 'fzfid', '%s e. Fin' % FZ)
    ak = '( %s /\\ k e. %s )' % (a, FZ)
    sk = mkst(w, ak)
    kn = sy(w, ak, sk([], 'simpr', 'k e. %s' % FZ), 'elfznn', 'k e. NN')
    kr = sk([kn], 'nnred', 'k e. RR')
    nrk = lift(w, nr, ak); nn0k = lift(w, nn0, ak)
    NUM = '( k + 1 )'; DEN = '( ( k + 1 ) + N )'
    numc = sk([sk([kn], 'peano2nnd', '%s e. NN' % NUM)], 'nncnd', '%s e. CC' % NUM)
    denn = sk([sk([kn], 'peano2nnd', '%s e. NN' % NUM), nn0k, w.inst('nnnn0addcl')], 'syl2anc', '%s e. NN' % DEN)
    denc = sk([denn], 'nncnd', '%s e. CC' % DEN); den0 = sk([denn], 'nnne0d', '%s =/= 0' % DEN)
    pd = st([fin, numc, denc, den0], 'fproddiv', 'prod_ k e. %s ( %s / %s ) = ( prod_ k e. %s %s / prod_ k e. %s %s )' % (FZ, NUM, DEN, FZ, NUM, FZ, DEN))

    def shifted(BODY, K, bst, A_, lo_eq_txt):
        """prod_ k e. FZ BODY = ( A_ FallFac N )"""
        kz = bst
        idk = w.s([], 'id', '( k = ( i - %s ) -> k = ( i - %s ) )' % (K, K))
        ceq, nb = w.congr(BODY, {'k': '( i - %s )' % K}, 'k = ( i - %s )' % K, {'k': idk})
        bodyc = numc if BODY == NUM else denc
        sh = st([kz, st([], '1zzd', '1 e. ZZ'), nz, bodyc, ceq], 'fprodshft', 'prod_ k e. %s %s = prod_ i e. ( ( 1 + %s ) ... ( N + %s ) ) %s' % (FZ, BODY, K, K, nb))
        RNG = '( ( 1 + %s ) ... ( N + %s ) )' % (K, K)
        ai = '( %s /\\ i e. %s )' % (a, RNG)
        si = mkst(w, ai)
        iz = sy(w, ai, si([], 'simpr', 'i e. %s' % RNG), 'elfzelz', 'i e. ZZ')
        cli = Closure(w, ai, {'i': ('RR', si([iz], 'zred', 'i e. RR')), 'N': ('RR', lift(w, nr, ai))})
        be = lin.lineq(w, ai, nb, 'i', closure=cli)
        pe = st([be], 'prodeq2dv', 'prod_ i e. %s %s = prod_ i e. %s i' % (RNG, nb, RNG))
        cln = Closure(w, a, {'N': ('RR', nr)})
        lo = lin.lineq(w, a, '( 1 + %s )' % K, '( %s - ( N - 1 ) )' % A_, closure=cln)
        hi = lin.lineq(w, a, '( N + %s )' % K, A_, closure=cln)
        FR = '( ( %s - ( N - 1 ) ) ... %s )' % (A_, A_)
        re = st([st([lo, hi], 'oveq12d', '%s = %s' % (RNG, FR))], 'prodeq1d', 'prod_ i e. %s i = prod_ i e. %s i' % (RNG, FR))
        cb = a1(w, a, w.s([w.s([], 'id', '( i = k -> i = k )')], 'cbvprodv', 'prod_ i e. %s i = prod_ k e. %s k' % (FR, FR)), 'prod_ i e. %s i = prod_ k e. %s k' % (FR, FR))
        l1 = st([sh, pe], 'eqtrd', 'prod_ k e. %s %s = prod_ i e. %s i' % (FZ, BODY, RNG))
        l2 = st([re, cb], 'eqtrd', 'prod_ i e. %s i = prod_ k e. %s k' % (RNG, FR))
        return st([l1, l2], 'eqtrd', 'prod_ k e. %s %s = prod_ k e. %s k' % (FZ, BODY, FR))
    A1 = '( N + 1 )'; A2 = '( ( 2 x. N ) + 1 )'
    one = st([], '1zzd', '1 e. ZZ')
    n1z = st([nz], 'peano2zd', '( N + 1 ) e. ZZ')
    p1 = shifted(NUM, '1', one, A1, None)
    p2 = shifted(DEN, '( N + 1 )', n1z, A2, None)
    # the falling factorials
    in1 = st([st([nn0, sy(w, a, nn0, 'peano2nn0', '( N + 1 ) e. NN0'),
                   lin.linarith(w, a, [], 'N <_ ( N + 1 )', leaves={'N': ('RR', nr)})], '3jca', '( N e. NN0 /\\ ( N + 1 ) e. NN0 /\\ N <_ ( N + 1 ) )'),
              a1(w, a, w.s([], 'elfz2nn0', '( N e. ( 0 ... ( N + 1 ) ) <-> ( N e. NN0 /\\ ( N + 1 ) e. NN0 /\\ N <_ ( N + 1 ) ) )'),
                 '( N e. ( 0 ... ( N + 1 ) ) <-> ( N e. NN0 /\\ ( N + 1 ) e. NN0 /\\ N <_ ( N + 1 ) ) )')], 'mpbird', 'N e. ( 0 ... ( N + 1 ) )')
    a2n = sy(w, a, st([a1(w, a, w.s([], '2nn0', '2 e. NN0'), '2 e. NN0'), nn0], 'nn0mulcld', '( 2 x. N ) e. NN0'), 'peano2nn0', '%s e. NN0' % A2)
    in2 = st([st([nn0, a2n, lin.linarith(w, a, [st([nn0], 'nn0ge0d', '0 <_ N')], 'N <_ %s' % A2, leaves={'N': ('RR', nr)})], '3jca',
                 '( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s )' % (A2, A2)),
              a1(w, a, w.s([], 'elfz2nn0', '( N e. ( 0 ... %s ) <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (A2, A2, A2)),
                 '( N e. ( 0 ... %s ) <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (A2, A2, A2))], 'mpbird', 'N e. ( 0 ... %s )' % A2)
    FF1 = '( %s FallFac N )' % A1; FF2 = '( %s FallFac N )' % A2
    f1 = sy(w, a, in1, 'fallfacval3', '%s = prod_ k e. ( ( %s - ( N - 1 ) ) ... %s ) k' % (FF1, A1, A1))
    f2 = sy(w, a, in2, 'fallfacval3', '%s = prod_ k e. ( ( %s - ( N - 1 ) ) ... %s ) k' % (FF2, A2, A2))
    q1 = st([p1, f1], 'eqtr4d', 'prod_ k e. %s %s = %s' % (FZ, NUM, FF1))
    q2 = st([p2, f2], 'eqtr4d', 'prod_ k e. %s %s = %s' % (FZ, DEN, FF2))
    b1 = sy(w, a, in1, 'bcfallfac', '( %s _C N ) = ( %s / ( ! ` N ) )' % (A1, FF1))
    b2 = sy(w, a, in2, 'bcfallfac', '( %s _C N ) = ( %s / ( ! ` N ) )' % (A2, FF2))
    bn = sy(w, a, sy(w, a, nn0, 'peano2nn0', '( N + 1 ) e. NN0'), 'bcnm1', '( %s _C ( %s - 1 ) ) = %s' % (A1, A1, A1))
    pc = st([st([nn0], 'nn0cnd', 'N e. CC'), st([], '1cnd', '1 e. CC')], 'pncand', '( %s - 1 ) = N' % A1)
    bn2 = st([st([pc], 'oveq2d', '( %s _C ( %s - 1 ) ) = ( %s _C N )' % (A1, A1, A1)), bn], 'eqtr3d', '( %s _C N ) = %s' % (A1, A1))
    ffc1 = st([q1, st([fin, numc], 'fprodcl', 'prod_ k e. %s %s e. CC' % (FZ, NUM))], 'eqeltrrd', '%s e. CC' % FF1)
    ffc2 = st([q2, st([fin, denc], 'fprodcl', 'prod_ k e. %s %s e. CC' % (FZ, DEN))], 'eqeltrrd', '%s e. CC' % FF2)
    ffn2 = st([q2, st([fin, denc, den0], 'fprodn0', 'prod_ k e. %s %s =/= 0' % (FZ, DEN))], 'eqnetrrd', '%s =/= 0' % FF2)
    fc = st([sy(w, a, nn0, 'faccl', '( ! ` N ) e. NN')], 'nncnd', '( ! ` N ) e. CC')
    fn = sy(w, a, nn0, 'facne0', '( ! ` N ) =/= 0')
    c7 = st([ffc1, ffc2, fc, ffn2, fn], 'divcan7d', '( ( %s / ( ! ` N ) ) / ( %s / ( ! ` N ) ) ) = ( %s / %s )' % (FF1, FF2, FF1, FF2))
    r1 = st([st([b1, b2], 'oveq12d', '( ( %s _C N ) / ( %s _C N ) ) = ( ( %s / ( ! ` N ) ) / ( %s / ( ! ` N ) ) )' % (A1, A2, FF1, FF2)), c7], 'eqtrd',
            '( ( %s _C N ) / ( %s _C N ) ) = ( %s / %s )' % (A1, A2, FF1, FF2))
    r2 = st([st([bn2], 'oveq1d', '( ( %s _C N ) / %s ) = ( %s / %s )' % (A1, BC21(), A1, BC21())), r1], 'eqtr3d', '( %s / %s ) = ( %s / %s )' % (A1, BC21(), FF1, FF2))
    lhs = st([pd, st([q1, q2], 'oveq12d', '( prod_ k e. %s %s / prod_ k e. %s %s ) = ( %s / %s )' % (FZ, NUM, FZ, DEN, FF1, FF2))], 'eqtrd',
             'prod_ k e. %s ( %s / %s ) = ( %s / %s )' % (FZ, NUM, DEN, FF1, FF2))
    w.qed([lhs, r2], 'eqtr4d', STATEMENTS['z5dqnid'])
    return w


def z5dbcl():
    w = W('z5dbcl', "C ( 2 n + 1 , n ) >_ 4 ^ n ( 2 n + 1 ) / ( n ( n + 1 ) ) for n >_ 4: C ( 2 n + 1 , n ) = C ( 2 n + 1 , n + 1 ) = "
                    "C ( 2 n , n ) ( 2 n + 1 ) / ( n + 1 ) (bccmpl, bcp1nk) and set.mm's bclbnd.")
    a = 'N e. ( ZZ>= ` 4 )'
    st = mkst(w, a)
    nu = st([], 'id', a)
    nn = sy(w, a, st([a1(w, a, w.s([], '4nn', '4 e. NN'), '4 e. NN'), nu], 'jca', '( 4 e. NN /\\ N e. ( ZZ>= ` 4 ) )'), 'eluznn', 'N e. NN')
    nn0 = st([nn], 'nnnn0d', 'N e. NN0'); nr = st([nn], 'nnred', 'N e. RR'); nc = st([nn], 'nncnd', 'N e. CC')
    A2 = '( ( 2 x. N ) + 1 )'; N2 = '( 2 x. N )'
    n2n0 = st([a1(w, a, w.s([], '2nn0', '2 e. NN0'), '2 e. NN0'), nn0], 'nn0mulcld', '%s e. NN0' % N2)
    a2n0 = sy(w, a, n2n0, 'peano2nn0', '%s e. NN0' % A2)
    cm = st([a2n0, st([nn], 'nnzd', 'N e. ZZ'), w.inst('bccmpl')], 'syl2anc', '%s = ( %s _C ( %s - N ) )' % (BC21(), A2, A2))
    cln = Closure(w, a, {'N': ('RR', nr)})
    e1 = lin.lineq(w, a, '( %s - N )' % A2, '( N + 1 )', closure=cln)
    cm2 = st([cm, st([e1], 'oveq2d', '( %s _C ( %s - N ) ) = ( %s _C ( N + 1 ) )' % (A2, A2, A2))], 'eqtrd', '%s = ( %s _C ( N + 1 ) )' % (BC21(), A2))
    inz = st([st([nn0, n2n0, lin.linarith(w, a, [st([nn], 'nnge1d', '1 <_ N')], 'N <_ %s' % N2, closure=cln)], '3jca', '( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s )' % (N2, N2)),
              a1(w, a, w.s([], 'elfz2nn0', '( N e. ( 0 ... %s ) <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (N2, N2, N2)),
                 '( N e. ( 0 ... %s ) <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (N2, N2, N2))], 'mpbird', 'N e. ( 0 ... %s )' % N2)
    bp = sy(w, a, inz, 'bcp1nk', '( %s _C ( N + 1 ) ) = ( ( %s _C N ) x. ( %s / ( N + 1 ) ) )' % (A2, N2, A2))
    C2 = '( %s _C N )' % N2
    bl = sy(w, a, nu, 'bclbnd', '( ( 4 ^ N ) / N ) < %s' % C2)
    n1rp = st([st([nn], 'peano2nnd', '( N + 1 ) e. NN')], 'nnrpd', '( N + 1 ) e. RR+')
    a2rp = st([sy(w, a, n2n0, 'nn0p1nn', '%s e. NN' % A2)], 'nnrpd', '%s e. RR+' % A2)
    fr = st([a2rp, n1rp], 'rpdivcld', '( %s / ( N + 1 ) ) e. RR+' % A2)
    c2r = st([sy(w, a, inz, 'bccl2', '%s e. NN' % C2)], 'nnred', '%s e. RR' % C2)
    q4 = st([st([a1(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), nn0], 'reexpcld', '( 4 ^ N ) e. RR'), st([nn], 'nnrpd', 'N e. RR+')], 'rerpdivcld', '( ( 4 ^ N ) / N ) e. RR')
    lt = st([q4, c2r, fr, bl], 'ltmul1dd', '( ( ( 4 ^ N ) / N ) x. ( %s / ( N + 1 ) ) ) < ( %s x. ( %s / ( N + 1 ) ) )' % (A2, C2, A2))
    dm = st([st([a1(w, a, w.s([], '4cn', '4 e. CC'), '4 e. CC'), nn0], 'expcld', '( 4 ^ N ) e. CC'),
             nc, st([a2rp], 'rpcnd', '%s e. CC' % A2), st([n1rp], 'rpcnd', '( N + 1 ) e. CC'), st([nn], 'nnne0d', 'N =/= 0'), st([n1rp], 'rpne0d', '( N + 1 ) =/= 0')],
            'divmuldivd', '( ( ( 4 ^ N ) / N ) x. ( %s / ( N + 1 ) ) ) = %s' % (A2, BCL()))
    val = st([cm2, bp], 'eqtrd', '%s = ( %s x. ( %s / ( N + 1 ) ) )' % (BC21(), C2, A2))
    bclr = st([dm, st([q4, st([fr], 'rpred', '( %s / ( N + 1 ) ) e. RR' % A2)], 'remulcld', '( ( ( 4 ^ N ) / N ) x. ( %s / ( N + 1 ) ) ) e. RR' % A2)], 'eqeltrrd', '%s e. RR' % BCL())
    bcr = st([sy(w, a, st([st([nn0, a2n0, lin.linarith(w, a, [st([nn], 'nnge1d', '1 <_ N')], 'N <_ %s' % A2, closure=cln)], '3jca', '( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s )' % (A2, A2)),
                                  a1(w, a, w.s([], 'elfz2nn0', '( N e. ( 0 ... %s ) <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (A2, A2, A2)),
                                     '( N e. ( 0 ... %s ) <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (A2, A2, A2))], 'mpbird', 'N e. ( 0 ... %s )' % A2), 'bccl2', '%s e. NN' % BC21())],
             'nnred', '%s e. RR' % BC21())
    w.qed([bclr, bcr, st([st([dm, lt], 'eqbrtrrd', '%s < ( %s x. ( %s / ( N + 1 ) ) )' % (BCL(), C2, A2)), val], 'breqtrrd', '%s < %s' % (BCL(), BC21()))], 'ltled', STATEMENTS['z5dbcl'])
    return w


def z5dlog2():
    w = W('z5dlog2', "log 2 >_ 56 / 81 (set.mm's log2tlbnd at N = 2: log 2 exceeds the partial sum 2 / 3 + 2 / 81 of its series).  "
                     "It makes 8 ^ n beat e ^ ( 2 n ) by the factor e ^ ( 2 n / 27 ) in the Gamma bound.")
    a = '2 e. NN0'
    st = mkst(w, a)
    L = '( log ` 2 )'
    TT = lambda n: '( 2 / ( ( 3 x. ( ( 2 x. %s ) + 1 ) ) x. ( 9 ^ %s ) ) )' % (n, n)
    S = 'sum_ n e. ( 0 ... ( 2 - 1 ) ) %s' % TT('n')
    C3 = '( 3 / ( ( 4 x. ( ( 2 x. 2 ) + 1 ) ) x. ( 9 ^ 2 ) ) )'
    lt = sy(w, a, st([], 'id', a), 'log2tlbnd', '( %s - %s ) e. ( 0 [,] %s )' % (L, S, C3))
    cl = Closure(w, a, {})
    c3r = cl.mem(C3, 'RR')
    el = st([st([], '0red', '0 e. RR'), c3r, w.inst('elicc2')], 'syl2anc', '( ( %s - %s ) e. ( 0 [,] %s ) <-> ( ( %s - %s ) e. RR /\\ 0 <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s ) )'
            % (L, S, C3, L, S, L, S, L, S, C3))
    ge = st([st([lt, el], 'mpbid', '( ( %s - %s ) e. RR /\\ 0 <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s )' % (L, S, L, S, L, S, C3))], 'simp2d', '0 <_ ( %s - %s )' % (L, S))
    # the partial sum
    r1 = a1(w, a, w.s([], '2m1e1', '( 2 - 1 ) = 1'), '( 2 - 1 ) = 1')
    rg = st([st([r1], 'oveq2d', '( 0 ... ( 2 - 1 ) ) = ( 0 ... 1 )'), a1(w, a, w.s([], 'fz01pr', '( 0 ... 1 ) = { 0 , 1 }'), '( 0 ... 1 ) = { 0 , 1 }')], 'eqtrd',
            '( 0 ... ( 2 - 1 ) ) = { 0 , 1 }')
    s1 = st([rg], 'sumeq1d', '%s = sum_ n e. { 0 , 1 } %s' % (S, TT('n')))
    c0, _ = w.congr(TT('n'), {'n': '0'}, 'n = 0', {'n': w.s([], 'id', '( n = 0 -> n = 0 )')})
    c1, _ = w.congr(TT('n'), {'n': '1'}, 'n = 1', {'n': w.s([], 'id', '( n = 1 -> n = 1 )')})
    tcc = st([cl.mem(TT('0'), 'CC'), cl.mem(TT('1'), 'CC')], 'jca', '( %s e. CC /\\ %s e. CC )' % (TT('0'), TT('1')))
    ex = st([a1(w, a, w.s([], 'c0ex', '0 e. _V'), '0 e. _V'), a1(w, a, w.s([], '1ex', '1 e. _V'), '1 e. _V')], 'jca', '( 0 e. _V /\\ 1 e. _V )')
    ne = a1(w, a, w.s([], '0ne1', '0 =/= 1'), '0 =/= 1')
    sp = w.s([c0, c1, tcc, ex, ne], 'sumpr', '( %s -> sum_ n e. { 0 , 1 } %s = ( %s + %s ) )' % (a, TT('n'), TT('0'), TT('1')))
    fact = lambda ref, f: a1(w, a, w.s([], ref, f), f)
    e0 = fact('2t0e0', '( 2 x. 0 ) = 0')
    x0 = sy(w, a, a1(w, a, w.s([], '9cn', '9 e. CC'), '9 e. CC'), 'exp0', '( 9 ^ 0 ) = 1')
    x1 = sy(w, a, a1(w, a, w.s([], '9cn', '9 e. CC'), '9 e. CC'), 'exp1', '( 9 ^ 1 ) = 9')
    ra, na = w.rewrite(TT('0'), {'( 2 x. 0 )': ('0', e0), '( 9 ^ 0 )': ('1', x0)}, a)
    rb, nb = w.rewrite(na, {'( 0 + 1 )': ('1', fact('0p1e1', '( 0 + 1 ) = 1'))}, a)
    rc, nc = w.rewrite(nb, {'( 3 x. 1 )': ('3', fact('3t1e3', '( 3 x. 1 ) = 3'))}, a)
    rd, nd = w.rewrite(nc, {'( 3 x. 1 )': ('3', fact('3t1e3', '( 3 x. 1 ) = 3'))}, a)
    assert nd == '( 2 / 3 )', nd
    t0 = st([st([ra, rb], 'eqtrd', '%s = %s' % (TT('0'), nb)), st([rc, rd], 'eqtrd', '%s = %s' % (nb, nd))], 'eqtrd',
                                                                              '%s = %s' % (TT('0'), nd))
    rA, nA = w.rewrite(TT('1'), {'( 2 x. 1 )': ('2', fact('2t1e2', '( 2 x. 1 ) = 2')), '( 9 ^ 1 )': ('9', x1)}, a)
    rB, nB = w.rewrite(nA, {'( 2 + 1 )': ('3', fact('2p1e3', '( 2 + 1 ) = 3'))}, a)
    rC, nC = w.rewrite(nB, {'( 3 x. 3 )': ('9', fact('3t3e9', '( 3 x. 3 ) = 9'))}, a)
    rD, nD = w.rewrite(nC, {'( 9 x. 9 )': ('; 8 1', fact('9t9e81', '( 9 x. 9 ) = ; 8 1'))}, a)
    assert nD == '( 2 / ; 8 1 )', nD
    t1 = st([st([rA, rB], 'eqtrd', '%s = %s' % (TT('1'), nB)), st([rC, rD], 'eqtrd', '%s = %s' % (nB, nD))], 'eqtrd', '%s = %s' % (TT('1'), nD))
    seq_ = st([st([s1, sp], 'eqtrd', '%s = ( %s + %s )' % (S, TT('0'), TT('1'))), st([t0, t1], 'oveq12d', '( %s + %s ) = ( ( 2 / 3 ) + ( 2 / ; 8 1 ) )' % (TT('0'), TT('1')))],
              'eqtrd', '%s = ( ( 2 / 3 ) + ( 2 / ; 8 1 ) )' % S)
    lr = st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')], 'relogcld', '%s e. RR' % L)
    sr = st([seq_, cl.mem('( ( 2 / 3 ) + ( 2 / ; 8 1 ) )', 'RR')], 'eqeltrd', '%s e. RR' % S)
    g = lin.linarith(w, a, [ge, seq_], '( ; 5 6 / ; 8 1 ) <_ %s' % L, leaves={L: ('RR', lr), S: ('RR', sr)}, atoms=[L, S])
    w.qed([w.s([], '2nn0', '2 e. NN0'), g], 'ax-mp', STATEMENTS['z5dlog2'])
    return w


def rpl(w, ante, v):
    """( ante -> v e. RR+ ) for a positive numeral literal v"""
    s_ = mkst(w, ante)
    return s_([a1(w, ante, num.real(w, v), '%s e. RR' % v), a1(w, ante, num.le_lit(w, '0', v, strict=True), '0 < %s' % v)], 'elrpd', '%s e. RR+' % v)


def z5dglin():
    w = W('z5dglin', "The linear core of the I8(b) numerics (z5dgnum) on class variables: A = log G, B = log u, C = log n, D = log ( n + 1 ), "
                     "E = log ( 2 n + 1 ), F = log ( n + 2 ), T = log 2, H = log 3, S = log 60: the bounds give A + u <_ S.")
    hs = hyps_of(w, 'z5dglin')
    a = 'ph'
    cl = Closure(w, a, {})
    for i, v in enumerate(GLV):
        cl.leaf(v, 'RR', hs[10 + i])
    g = lin.linarith(w, a, hs[:10], '( A + U ) <_ S', closure=cl, products=True, name='qed')
    if w.lines[-1].split(':', 1)[0] != 'qed':
        last = w.lines.pop()
        w.lines.append('qed:' + last.split(':', 1)[1])
    return w


def z5dgsm():
    w = W('z5dgsm', "The numerics of I8(b) for 1 / 2 <_ | Im z | < 4: from G u <_ 1, G <_ 60 e ^ -u since e ^ u <_ 60 u there "
                     "(e ^ 2 <_ 9 <_ 60 u for u <_ 2, e ^ 4 <_ 81 <_ 60 u for u >_ 2; e < 3).")
    a = ante('z5dgsm')
    st = mkst(w, a)
    hu = st([], 'simp1', '( U e. RR /\\ ( 1 / 2 ) <_ U /\\ U < 4 )')
    hg = st([], 'simp2', '( G e. RR /\\ 0 <_ G )')
    hm = st([], 'simp3', '( G x. U ) <_ 1')
    ur = st([hu], 'simp1d', 'U e. RR'); uh = st([hu], 'simp2d', '( 1 / 2 ) <_ U'); u4 = st([hu], 'simp3d', 'U < 4')
    gr = st([hg], 'simpld', 'G e. RR'); g0 = st([hg], 'simprd', '0 <_ G')
    E1 = '( exp ` 1 )'; E2 = '( exp ` 2 )'; E4 = '( exp ` 4 )'; EU = '( exp ` U )'
    e1r = st([st([], '1red', '1 e. RR')], 'reefcld', '%s e. RR' % E1)
    e13 = a1(w, a, w.s([w.s([], 'df-e', '_e = %s' % E1), w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')], 'eqbrtrri', '%s < 3' % E1), '%s < 3' % E1)
    e10 = sy(w, a, st([], '1red', '1 e. RR'), 'efgt0', '0 < %s' % E1)
    ef2 = st([st([], '1cnd', '1 e. CC'), a1(w, a, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ'), w.inst('efexp')], 'syl2anc', '( exp ` ( 2 x. 1 ) ) = ( %s ^ 2 )' % E1)
    ef2b = st([st([a1(w, a, w.s([], '2t1e2', '( 2 x. 1 ) = 2'), '( 2 x. 1 ) = 2')], 'fveq2d', '( exp ` ( 2 x. 1 ) ) = %s' % E2), ef2], 'eqtr3d', '%s = ( %s ^ 2 )' % (E2, E1))
    sq = st([st([e1r, st([e10], 'ltled', '0 <_ %s' % E1)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (E1, E1)),
             st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), st([e1r, a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), e13], 'ltled', '%s <_ 3' % E1)], 'jca',
                '( 3 e. RR /\\ %s <_ 3 )' % E1), w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( 3 ^ 2 )' % E1)
    e29 = st([st([ef2b, sq], 'eqbrtrd', '%s <_ ( 3 ^ 2 )' % E2), a1(w, a, w.s([], 'sq3', '( 3 ^ 2 ) = 9'), '( 3 ^ 2 ) = 9')], 'breqtrd', '%s <_ 9' % E2)
    ef4 = st([st([], '2cnd', '2 e. CC'), st([], '2cnd', '2 e. CC'), w.inst('efadd')], 'syl2anc', '( exp ` ( 2 + 2 ) ) = ( %s x. %s )' % (E2, E2))
    ef4b = st([st([a1(w, a, w.s([], '2p2e4', '( 2 + 2 ) = 4'), '( 2 + 2 ) = 4')], 'fveq2d', '( exp ` ( 2 + 2 ) ) = %s' % E4), ef4], 'eqtr3d', '%s = ( %s x. %s )' % (E4, E2, E2))
    e2r = st([litr(w, a, '2')], 'reefcld', '%s e. RR' % E2)
    e20 = sy(w, a, litr(w, a, '2'), 'efgt0', '0 < %s' % E2)
    cle = Closure(w, a, {E2: ('RR', e2r), E4: ('RR', st([litr(w, a, '4')], 'reefcld', '%s e. RR' % E4)), 'U': ('RR', ur), EU: ('RR', st([ur], 'reefcld', '%s e. RR' % EU))})
    for at in (E2, E4, EU):
        cle.atom(at)
    e481 = lin.linarith(w, a, [ef4b, e29, st([e20], 'ltled', '0 <_ %s' % E2)], '%s <_ ; 8 1' % E4, closure=cle, products=True)
    # e ^ U <_ 60 U
    GO = '%s <_ ( ; 6 0 x. U )' % EU
    ca = '( %s /\\ U <_ 2 )' % a
    sa = mkst(w, ca)
    la = sa([sa([], 'simpr', 'U <_ 2'), sa([lift(w, ur, ca), litr(w, ca, '2'), w.inst('efle')], 'syl2anc', '( U <_ 2 <-> %s <_ %s )' % (EU, E2))], 'mpbid', '%s <_ %s' % (EU, E2))
    cla = Closure(w, ca, {E2: ('RR', lift(w, e2r, ca)), 'U': ('RR', lift(w, ur, ca)), EU: ('RR', lift(w, st([ur], 'reefcld', '%s e. RR' % EU), ca))})
    for at in (E2, EU):
        cla.atom(at)
    ga = lin.linarith(w, ca, [la, lift(w, e29, ca), lift(w, uh, ca)], GO, closure=cla)
    cb = '( %s /\\ -. U <_ 2 )' % a
    sb = mkst(w, cb)
    u2 = sb([sb([], 'simpr', '-. U <_ 2'), sb([litr(w, cb, '2'), lift(w, ur, cb)], 'ltnled', '( 2 < U <-> -. U <_ 2 )')], 'mpbird', '2 < U')
    lb = sb([sb([lift(w, ur, cb), litr(w, cb, '4'), lift(w, u4, cb)], 'ltled', 'U <_ 4'), sb([lift(w, ur, cb), litr(w, cb, '4'), w.inst('efle')], 'syl2anc', '( U <_ 4 <-> %s <_ %s )' % (EU, E4))],
            'mpbid', '%s <_ %s' % (EU, E4))
    clb = Closure(w, cb, {E4: ('RR', lift(w, st([litr(w, a, '4')], 'reefcld', '%s e. RR' % E4), cb)), 'U': ('RR', lift(w, ur, cb)), EU: ('RR', lift(w, st([ur], 'reefcld', '%s e. RR' % EU), cb))})
    for at in (E4, EU):
        clb.atom(at)
    gb = lin.linarith(w, cb, [lb, lift(w, e481, cb), u2], GO, closure=clb)
    eu = w.s([ga, gb], 'pm2.61dan', '( %s -> %s )' % (a, GO))
    # G e ^ U <_ G ( 60 U ) <_ 60
    eur = st([ur], 'reefcld', '%s e. RR' % EU)
    m = st([eur, st([litr(w, a, '; 6 0'), ur], 'remulcld', '( ; 6 0 x. U ) e. RR'), gr, g0, eu], 'lemul2ad', '( G x. %s ) <_ ( G x. ( ; 6 0 x. U ) )' % EU)
    clg = Closure(w, a, {'G': ('RR', gr), 'U': ('RR', ur), EU: ('RR', eur)})
    clg.atom(EU)
    g60 = lin.linarith(w, a, [m, hm], '( G x. %s ) <_ ; 6 0' % EU, closure=clg, products=True)
    eurp = st([ur], 'rpefcld', '%s e. RR+' % EU)
    gle2 = st([g60, st([gr, litr(w, a, '; 6 0'), eurp], 'lemuldivd', '( ( G x. %s ) <_ ; 6 0 <-> G <_ ( ; 6 0 / %s ) )' % (EU, EU))], 'mpbid', 'G <_ ( ; 6 0 / %s )' % EU)
    en = sy(w, a, st([ur], 'recnd', 'U e. CC'), 'efneg', '( exp ` -u U ) = ( 1 / %s )' % EU)
    dv = st([a1(w, a, num.cc(w, '; 6 0'), '; 6 0 e. CC'), st([eurp], 'rpcnd', '%s e. CC' % EU), st([eurp], 'rpne0d', '%s =/= 0' % EU)], 'divrecd',
            '( ; 6 0 / %s ) = ( ; 6 0 x. ( 1 / %s ) )' % (EU, EU))
    rh = st([dv, st([en], 'oveq2d', '%s = ( ; 6 0 x. ( 1 / %s ) )' % (E60('U'), EU))], 'eqtr4d', '( ; 6 0 / %s ) = %s' % (EU, E60('U')))
    w.qed([gle2, rh], 'breqtrd', STATEMENTS['z5dgsm'])
    return w


def z5dgam():
    w = W('z5dgam', "Blueprint interface I8(b) (Lean norm_Gamma_le_exp_neg_im, constant CGamma' = 60): | Gamma ( z ) | <_ 60 e ^ -| Im z | on "
                    "0 <_ Re z <_ 1, | Im z | >_ 1 / 2, from set.mm's Euler product: | Gamma ( z ) z | <_ prod ( 1 ... n ) ( m + Re z ) / | z + m | "
                    "(z5dgzp) at n = |_ | Im z |, each squared ratio <_ 2 ( ( m + 1 ) / ( m + 1 + n ) ) ^ 2 (z5dfac), whose product is "
                    "2 ^ n ( ( n + 1 ) / C ( 2 n + 1 , n ) ) ^ 2 (z5dqnid, z5dbcl), and the numerics z5dgnum, z5dgsm.")
    a = ante('z5dgam')
    st = mkst(w, a)
    U_ = AIZ
    zc = st([], 'simpl', 'Z e. CC')
    hh = st([], 'simpr', '( 0 <_ %s /\\ %s <_ 1 /\\ ( 1 / 2 ) <_ %s )' % (RZ, RZ, U_))
    x0 = st([hh], 'simp1d', '0 <_ %s' % RZ); x1 = st([hh], 'simp2d', '%s <_ 1' % RZ); uh = st([hh], 'simp3d', '( 1 / 2 ) <_ %s' % U_)
    ur = st([st([st([zc], 'imcld', '( Im ` Z ) e. RR')], 'recnd', '( Im ` Z ) e. CC')], 'abscld', '%s e. RR' % U_)
    # Z is not a nonpositive integer
    az = '( %s /\\ Z e. ZZ )' % a
    sz = mkst(w, az)
    im0 = sy(w, az, sy(w, az, sz([], 'simpr', 'Z e. ZZ'), 'zre', 'Z e. RR'), 'reim0', '( Im ` Z ) = 0')
    ab0 = sz([sz([im0], 'fveq2d', '%s = ( abs ` 0 )' % U_), a1(w, az, w.s([], 'abs0', '( abs ` 0 ) = 0'), '( abs ` 0 ) = 0')], 'eqtrd', '%s = 0' % U_)
    lt0 = lin.linarith(w, az, [ab0], '%s < ( 1 / 2 )' % U_, leaves={U_: ('RR', lift(w, ur, az))}, atoms=[U_])
    nlt = sz([lift(w, uh, az), sz([litr(w, az, '( 1 / 2 )'), lift(w, ur, az)], 'lenltd', '( ( 1 / 2 ) <_ %s <-> -. %s < ( 1 / 2 ) )' % (U_, U_))], 'mpbid', '-. %s < ( 1 / 2 )' % U_)
    nz_ = w.s([lt0, nlt], 'pm2.65da', '( %s -> -. Z e. ZZ )' % a)
    nzn = st([nz_, a1(w, a, w.s([], 'eldifi', '( Z e. ( ZZ \\ NN ) -> Z e. ZZ )'), '( Z e. ( ZZ \\ NN ) -> Z e. ZZ )')], 'mtod', '-. Z e. ( ZZ \\ NN )')
    zd = st([st([zc, nzn], 'jca', '( Z e. CC /\\ -. Z e. ( ZZ \\ NN ) )'), a1(w, a, w.s([], 'eldif', '( Z e. ( CC \\ ( ZZ \\ NN ) ) <-> ( Z e. CC /\\ -. Z e. ( ZZ \\ NN ) ) )'),
                                                                                   '( Z e. ( CC \\ ( ZZ \\ NN ) ) <-> ( Z e. CC /\\ -. Z e. ( ZZ \\ NN ) ) )')],
            'mpbird', 'Z e. ( CC \\ ( ZZ \\ NN ) )')
    GZ = '( _G ` Z )'; G = '( abs ` %s )' % GZ
    gc = sy(w, a, zd, 'gamcl', '%s e. CC' % GZ)
    gr = st([gc], 'abscld', '%s e. RR' % G); g0 = st([gc], 'absge0d', '0 <_ %s' % G)
    # G u <_ | Gamma ( Z ) Z |
    zabs = st([zc], 'abscld', '( abs ` Z ) e. RR')
    ule = sy(w, a, zc, 'absimle', '%s <_ ( abs ` Z )' % U_)
    gu = st([ur, zabs, gr, g0, ule], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( abs ` Z ) )' % (G, U_, G))
    am = st([gc, zc, w.inst('absmul')], 'syl2anc', '( abs ` ( %s x. Z ) ) = ( %s x. ( abs ` Z ) )' % (GZ, G))
    gu2 = st([gu, am], 'breqtrrd', '( %s x. %s ) <_ ( abs ` ( %s x. Z ) )' % (G, U_, GZ))
    AGZ = '( abs ` ( %s x. Z ) )' % GZ
    zs = st([zd, st([x0, x1], 'jca', STRIP)], 'jca', '( Z e. ( CC \\ ( ZZ \\ NN ) ) /\\ %s )' % STRIP)
    GOAL = '%s <_ %s' % (G, E60(U_))
    # | Im Z | < 4
    c3 = '( %s /\\ -. 4 <_ %s )' % (a, U_)
    s3 = mkst(w, c3)
    L3 = lambda x: lift(w, x, c3)
    u4 = s3([s3([], 'simpr', '-. 4 <_ %s' % U_), s3([L3(ur), litr(w, c3, '4')], 'ltnled', '( %s < 4 <-> -. 4 <_ %s )' % (U_, U_))], 'mpbird', '%s < 4' % U_)
    gz0 = s3([s3([L3(zs), a1(w, c3, w.s([], '0nn0', '0 e. NN0'), '0 e. NN0')], 'jca', '( ( Z e. ( CC \\ ( ZZ \\ NN ) ) /\\ %s ) /\\ 0 e. NN0 )' % STRIP), w.inst('z5dgzp')], 'syl',
             '%s <_ prod_ k e. ( 1 ... 0 ) %s' % (AGZ, RAT('k')))
    p1 = s3([s3([a1(w, c3, w.s([], 'fz10', '( 1 ... 0 ) = (/)'), '( 1 ... 0 ) = (/)')], 'prodeq1d', 'prod_ k e. ( 1 ... 0 ) %s = prod_ k e. (/) %s' % (RAT('k'), RAT('k'))),
             a1(w, c3, w.s([], 'prod0', 'prod_ k e. (/) %s = 1' % RAT('k')), 'prod_ k e. (/) %s = 1' % RAT('k'))], 'eqtrd', 'prod_ k e. ( 1 ... 0 ) %s = 1' % RAT('k'))
    agzr3 = s3([s3([L3(gc), L3(zc)], 'mulcld', '( %s x. Z ) e. CC' % GZ)], 'abscld', '%s e. RR' % AGZ)
    gle1 = s3([s3([L3(gr), L3(ur)], 'remulcld', '( %s x. %s ) e. RR' % (G, U_)), agzr3, s3([], '1red', '1 e. RR'), L3(gu2), s3([gz0, p1], 'breqtrd', '%s <_ 1' % AGZ)],
              'letrd', '( %s x. %s ) <_ 1' % (G, U_))
    g_3 = s3([s3([s3([L3(ur), L3(uh), u4], '3jca', '( %s e. RR /\\ ( 1 / 2 ) <_ %s /\\ %s < 4 )' % (U_, U_, U_)), s3([L3(gr), L3(g0)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (G, G)), gle1],
                 '3jca', '( ( %s e. RR /\\ ( 1 / 2 ) <_ %s /\\ %s < 4 ) /\\ ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s x. %s ) <_ 1 )' % (U_, U_, U_, G, G, G, U_)), w.inst('z5dgsm')],
             'syl', GOAL)
    # | Im Z | >_ 4
    c4 = '( %s /\\ 4 <_ %s )' % (a, U_)
    s4 = mkst(w, c4)
    L4 = lambda x: lift(w, x, c4)
    n_ = '( |_ ` %s )' % U_
    nz = s4([L4(ur)], 'flcld', '%s e. ZZ' % n_)
    n4 = s4([s4([], 'simpr', '4 <_ %s' % U_), s4([L4(ur), a1(w, c4, w.s([], '4z', '4 e. ZZ'), '4 e. ZZ'), w.inst('flge')], 'syl2anc', '( 4 <_ %s <-> 4 <_ %s )' % (U_, n_))], 'mpbid', '4 <_ %s' % n_)
    nu = s4([s4([a1(w, c4, w.s([], '4z', '4 e. ZZ'), '4 e. ZZ'), nz, n4], '3jca', '( 4 e. ZZ /\\ %s e. ZZ /\\ 4 <_ %s )' % (n_, n_)),
             a1(w, c4, w.s([], 'eluz2', '( %s e. ( ZZ>= ` 4 ) <-> ( 4 e. ZZ /\\ %s e. ZZ /\\ 4 <_ %s ) )' % (n_, n_, n_)), '( %s e. ( ZZ>= ` 4 ) <-> ( 4 e. ZZ /\\ %s e. ZZ /\\ 4 <_ %s ) )' % (n_, n_, n_))],
            'mpbird', '%s e. ( ZZ>= ` 4 )' % n_)
    nn = sy(w, c4, s4([a1(w, c4, w.s([], '4nn', '4 e. NN'), '4 e. NN'), nu], 'jca', '( 4 e. NN /\\ %s e. ( ZZ>= ` 4 ) )' % n_), 'eluznn', '%s e. NN' % n_)
    nn0 = s4([nn], 'nnnn0d', '%s e. NN0' % n_)
    nle = sy(w, c4, L4(ur), 'flle', '%s <_ %s' % (n_, U_))
    ult = sy(w, c4, L4(ur), 'flltp1', '%s < ( %s + 1 )' % (U_, n_))
    P = 'prod_ k e. ( 1 ... %s ) %s' % (n_, RAT('k'))
    gzn = s4([s4([L4(zs), nn0], 'jca', '( ( Z e. ( CC \\ ( ZZ \\ NN ) ) /\\ %s ) /\\ %s e. NN0 )' % (STRIP, n_)), w.inst('z5dgzp')], 'syl', '%s <_ %s' % (AGZ, P))
    FZ = '( 1 ... %s )' % n_
    fin = s4([], 'fzfid', '%s e. Fin' % FZ)
    ak = '( %s /\\ k e. %s )' % (c4, FZ)
    sk = mkst(w, ak)
    kn = sy(w, ak, sk([], 'simpr', 'k e. %s' % FZ), 'elfznn', 'k e. NN')
    rk = ratfacts(w, ak, lift(w, zc, ak), lift(w, x0, ak), lift(w, x1, ak), kn)
    QKn = QK('k', n_)
    fac = sk([sk([sk([lift(w, zc, ak), sk([lift(w, x0, ak), lift(w, x1, ak)], 'jca', STRIP)], 'jca', '( Z e. CC /\\ %s )' % STRIP),
                  sk([lift(w, nn0, ak), lift(w, nle, ak)], 'jca', '( %s e. NN0 /\\ %s <_ %s )' % (n_, n_, U_)), kn], '3jca',
                 '( ( Z e. CC /\\ %s ) /\\ ( %s e. NN0 /\\ %s <_ %s ) /\\ k e. NN )' % (STRIP, n_, n_, U_)), w.inst('z5dfac')], 'syl', '( %s ^ 2 ) <_ ( 2 x. ( %s ^ 2 ) )' % (RAT('k'), QKn))
    # QK facts
    kp1 = sk([kn], 'peano2nnd', '( k + 1 ) e. NN')
    qden = sk([kp1, lift(w, nn0, ak), w.inst('nnnn0addcl')], 'syl2anc', '( ( k + 1 ) + %s ) e. NN' % n_)
    qkr = sk([sk([kp1], 'nnred', '( k + 1 ) e. RR'), sk([qden], 'nnrpd', '( ( k + 1 ) + %s ) e. RR+' % n_)], 'rerpdivcld', '%s e. RR' % QKn)
    rr_ = rk['rr']
    rsq = sk([rr_], 'resqcld', '( %s ^ 2 ) e. RR' % RAT('k'))
    r20 = sk([rr_], 'sqge0d', '0 <_ ( %s ^ 2 )' % RAT('k'))
    t2q = sk([litr(w, ak, '2'), sk([qkr], 'resqcld', '( %s ^ 2 ) e. RR' % QKn)], 'remulcld', '( 2 x. ( %s ^ 2 ) ) e. RR' % QKn)
    nf = w.s([], 'nfv', 'F/ k %s' % c4)
    ple = w.s([nf, fin, rsq, r20, t2q, fac], 'fprodle', '( %s -> prod_ k e. %s ( %s ^ 2 ) <_ prod_ k e. %s ( 2 x. ( %s ^ 2 ) ) )' % (c4, FZ, RAT('k'), FZ, QKn))
    # prod of squares = square of prod
    rc = sk([rr_], 'recnd', '%s e. CC' % RAT('k')); qc = sk([qkr], 'recnd', '%s e. CC' % QKn)
    sqk = sk([rc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (RAT('k'), RAT('k'), RAT('k')))
    pr1 = s4([sqk], 'prodeq2dv', 'prod_ k e. %s ( %s ^ 2 ) = prod_ k e. %s ( %s x. %s )' % (FZ, RAT('k'), FZ, RAT('k'), RAT('k')))
    pm1 = s4([fin, rc, rc], 'fprodmul', 'prod_ k e. %s ( %s x. %s ) = ( %s x. %s )' % (FZ, RAT('k'), RAT('k'), P, P))
    pc = s4([fin, rc], 'fprodcl', '%s e. CC' % P)
    psq = s4([pc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (P, P, P))
    pP = s4([psq, s4([pr1, pm1], 'eqtrd', 'prod_ k e. %s ( %s ^ 2 ) = ( %s x. %s )' % (FZ, RAT('k'), P, P))], 'eqtr4d', '( %s ^ 2 ) = prod_ k e. %s ( %s ^ 2 )' % (P, FZ, RAT('k')))
    PQ = 'prod_ k e. %s %s' % (FZ, QKn)
    q2c = sk([sk([qkr], 'resqcld', '( %s ^ 2 ) e. RR' % QKn)], 'recnd', '( %s ^ 2 ) e. CC' % QKn)
    pm2 = s4([fin, sk([], '2cnd', '2 e. CC'), q2c], 'fprodmul', 'prod_ k e. %s ( 2 x. ( %s ^ 2 ) ) = ( prod_ k e. %s 2 x. prod_ k e. %s ( %s ^ 2 ) )' % (FZ, QKn, FZ, FZ, QKn))
    pcst = s4([fin, s4([], '2cnd', '2 e. CC'), w.inst('fprodconst')], 'syl2anc', 'prod_ k e. %s 2 = ( 2 ^ ( # ` %s ) )' % (FZ, FZ))
    hsh = sy(w, c4, nn0, 'hashfz1', '( # ` %s ) = %s' % (FZ, n_))
    p2n = s4([pcst, s4([hsh], 'oveq2d', '( 2 ^ ( # ` %s ) ) = ( 2 ^ %s )' % (FZ, n_))], 'eqtrd', 'prod_ k e. %s 2 = ( 2 ^ %s )' % (FZ, n_))
    sqq = sk([qc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (QKn, QKn, QKn))
    pq1 = s4([s4([sqq], 'prodeq2dv', 'prod_ k e. %s ( %s ^ 2 ) = prod_ k e. %s ( %s x. %s )' % (FZ, QKn, FZ, QKn, QKn)), s4([fin, qc, qc], 'fprodmul',
              'prod_ k e. %s ( %s x. %s ) = ( %s x. %s )' % (FZ, QKn, QKn, PQ, PQ))], 'eqtrd', 'prod_ k e. %s ( %s ^ 2 ) = ( %s x. %s )' % (FZ, QKn, PQ, PQ))
    pqc = s4([fin, qc], 'fprodcl', '%s e. CC' % PQ)
    pq2 = s4([pq1, s4([pqc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (PQ, PQ, PQ))], 'eqtr4d', 'prod_ k e. %s ( %s ^ 2 ) = ( %s ^ 2 )' % (FZ, QKn, PQ))
    qid = sy(w, c4, nn0, 'z5dqnid', '%s = ( ( %s + 1 ) / %s )' % (PQ, n_, BC21(n_)))
    CQ = '( ( %s + 1 ) / %s )' % (n_, BC21(n_))
    pq3 = s4([pq2, s4([qid], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (PQ, CQ))], 'eqtrd', 'prod_ k e. %s ( %s ^ 2 ) = ( %s ^ 2 )' % (FZ, QKn, CQ))
    rhs = s4([pm2, s4([p2n, pq3], 'oveq12d', '( prod_ k e. %s 2 x. prod_ k e. %s ( %s ^ 2 ) ) = ( ( 2 ^ %s ) x. ( %s ^ 2 ) )' % (FZ, FZ, QKn, n_, CQ))], 'eqtrd',
             'prod_ k e. %s ( 2 x. ( %s ^ 2 ) ) = ( ( 2 ^ %s ) x. ( %s ^ 2 ) )' % (FZ, QKn, n_, CQ))
    P2 = s4([s4([pP, ple], 'eqbrtrd', '( %s ^ 2 ) <_ prod_ k e. %s ( 2 x. ( %s ^ 2 ) )' % (P, FZ, QKn)), rhs], 'breqtrd', '( %s ^ 2 ) <_ ( ( 2 ^ %s ) x. ( %s ^ 2 ) )' % (P, n_, CQ))
    # ( G u ) ^ 2 <_ P ^ 2
    gur = s4([L4(gr), L4(ur)], 'remulcld', '( %s x. %s ) e. RR' % (G, U_))
    gu0 = s4([L4(gr), L4(ur), L4(g0), lin.linarith(w, c4, [s4([], 'simpr', '4 <_ %s' % U_)], '0 <_ %s' % U_, leaves={U_: ('RR', L4(ur))}, atoms=[U_])], 'mulge0d',
             '0 <_ ( %s x. %s )' % (G, U_))
    agzr = s4([s4([L4(gc), L4(zc)], 'mulcld', '( %s x. Z ) e. CC' % GZ)], 'abscld', '%s e. RR' % AGZ)
    pr = s4([fin, rr_], 'fprodrecl', '%s e. RR' % P)
    gup = s4([gur, agzr, pr, L4(gu2), gzn], 'letrd', '( %s x. %s ) <_ %s' % (G, U_, P))
    gsq = s4([s4([gur, gu0], 'jca', '( ( %s x. %s ) e. RR /\\ 0 <_ ( %s x. %s ) )' % (G, U_, G, U_)), s4([pr, gup], 'jca', '( %s e. RR /\\ ( %s x. %s ) <_ %s )' % (P, G, U_, P)),
              w.inst('le2sq2')], 'syl2anc', '( ( %s x. %s ) ^ 2 ) <_ ( %s ^ 2 )' % (G, U_, P))
    smd = s4([s4([L4(gr)], 'recnd', '%s e. CC' % G), s4([L4(ur)], 'recnd', '%s e. CC' % U_)], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (G, U_, G, U_))
    G2U2 = '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (G, U_)
    g2u2r = s4([s4([L4(gr)], 'resqcld', '( %s ^ 2 ) e. RR' % G), s4([L4(ur)], 'resqcld', '( %s ^ 2 ) e. RR' % U_)], 'remulcld', '%s e. RR' % G2U2)
    RH = '( ( 2 ^ %s ) x. ( %s ^ 2 ) )' % (n_, CQ)
    bcn = sy(w, c4, s4([s4([nn0, sy(w, c4, s4([a1(w, c4, w.s([], '2nn0', '2 e. NN0'), '2 e. NN0'), nn0], 'nn0mulcld', '( 2 x. %s ) e. NN0' % n_), 'peano2nn0',
                                           '( ( 2 x. %s ) + 1 ) e. NN0' % n_),
                            lin.linarith(w, c4, [s4([nn], 'nnge1d', '1 <_ %s' % n_)], '%s <_ ( ( 2 x. %s ) + 1 )' % (n_, n_), leaves={n_: ('RR', s4([nn], 'nnred', '%s e. RR' % n_))},
                                         atoms=[n_])], '3jca', '( %s e. NN0 /\\ ( ( 2 x. %s ) + 1 ) e. NN0 /\\ %s <_ ( ( 2 x. %s ) + 1 ) )' % (n_, n_, n_, n_)),
                        a1(w, c4, w.s([], 'elfz2nn0', '( %s e. ( 0 ... ( ( 2 x. %s ) + 1 ) ) <-> ( %s e. NN0 /\\ ( ( 2 x. %s ) + 1 ) e. NN0 /\\ %s <_ ( ( 2 x. %s ) + 1 ) ) )'
                                         % (n_, n_, n_, n_, n_, n_)),
                           '( %s e. ( 0 ... ( ( 2 x. %s ) + 1 ) ) <-> ( %s e. NN0 /\\ ( ( 2 x. %s ) + 1 ) e. NN0 /\\ %s <_ ( ( 2 x. %s ) + 1 ) ) )' % (n_, n_, n_, n_, n_, n_))],
                       'mpbird', '%s e. ( 0 ... ( ( 2 x. %s ) + 1 ) )' % (n_, n_)), 'bccl2', '%s e. NN' % BC21(n_))
    cnr = s4([bcn], 'nnred', '%s e. RR' % BC21(n_))
    cnrp = s4([bcn], 'nnrpd', '%s e. RR+' % BC21(n_))
    rhr = s4([s4([litr(w, c4, '2'), nn0], 'reexpcld', '( 2 ^ %s ) e. RR' % n_),
              s4([s4([s4([s4([nn], 'peano2nnd', '( %s + 1 ) e. NN' % n_)], 'nnred', '( %s + 1 ) e. RR' % n_), cnrp], 'rerpdivcld', '%s e. RR' % CQ)], 'resqcld', '( %s ^ 2 ) e. RR' % CQ)],
             'remulcld', '%s e. RR' % RH)
    hm = s4([g2u2r, s4([pr], 'resqcld', '( %s ^ 2 ) e. RR' % P), rhr, s4([smd, gsq], 'eqbrtrrd', '%s <_ ( %s ^ 2 )' % (G2U2, P)), P2], 'letrd', '%s <_ %s' % (G2U2, RH))
    bl = sy(w, c4, nu, 'z5dbcl', '%s <_ %s' % (BCL(n_), BC21(n_)))
    A1 = s4([nu, s4([L4(ur), nle, ult], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s < ( %s + 1 ) )' % (U_, n_, U_, U_, n_))], 'jca',
            '( %s e. ( ZZ>= ` 4 ) /\\ ( %s e. RR /\\ %s <_ %s /\\ %s < ( %s + 1 ) ) )' % (n_, U_, n_, U_, U_, n_))
    A2 = s4([s4([L4(gr), L4(g0)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (G, G)), s4([cnr, bl], 'jca', '( %s e. RR /\\ %s <_ %s )' % (BC21(n_), BCL(n_), BC21(n_)))], 'jca',
            '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ %s <_ %s ) )' % (G, G, BC21(n_), BCL(n_), BC21(n_)))
    AA = '( ( %s e. ( ZZ>= ` 4 ) /\\ ( %s e. RR /\\ %s <_ %s /\\ %s < ( %s + 1 ) ) ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ %s <_ %s ) ) /\\ %s <_ %s )' % (
        n_, U_, n_, U_, U_, n_, G, G, BC21(n_), BCL(n_), BC21(n_), G2U2, RH)
    g_4 = s4([s4([A1, A2, hm], '3jca', AA), w.inst('z5dgnum')], 'syl', GOAL)
    w.qed([g_4, g_3], 'pm2.61dan', STATEMENTS['z5dgam'])
    return w


def z5dgamh():
    w = W('z5dgamh', "I8(b) in the form the pole-term lemma takes it (Z5c's GAMH at K = 60; the argument fun z hz0 hz1 hz2 => "
                     "norm_Gamma_le_exp_neg_im z hz0 hz1 hz2 of detector_lower_bound_of_P1).")
    sub = lambda f: f.replace('Z', 'z')
    inst = sub(STATEMENTS['z5dgam'])
    s1 = w.s([], 'z5dgam', inst)
    a_, c_ = split_imp(inst)
    parts = a_[2:-2].split(' /\\ ', 1)
    s2 = w.s([s1], 'ex', '( z e. CC -> ( %s -> %s ) )' % (parts[1], c_))
    w.qed([s2], 'rgen', STATEMENTS['z5dgamh'])
    return w


def rwall(w, ante, expr, rules):
    """( ante -> expr = expr' ) rewriting with rules until nothing changes; returns (step, new) or (None, expr)"""
    steps = []; cur = expr
    for _ in range(12):
        hit = {k: v for k, v in rules.items() if k in cur.split(' ') or (' %s ' % k) in (' %s ' % cur)}
        if not hit:
            break
        st_, new = w.rewrite(cur, hit, ante)
        if new == cur:
            break
        steps.append((st_, cur, new)); cur = new
    if not steps:
        return None, expr
    s0 = steps[0][0]
    for st_, old, new in steps[1:]:
        s0 = w.s([s0, st_], 'eqtrd', '( %s -> %s = %s )' % (ante, expr, new))
    return s0, cur


def z5dgnum():
    w = W('z5dgnum', "The numerics of I8(b) for | Im z | >_ 4, on logarithms: from ( G u ) ^ 2 <_ 2 ^ n ( ( n + 1 ) / C ) ^ 2 with "
                     "C >_ 4 ^ n ( 2 n + 1 ) / ( n ( n + 1 ) ) and n <_ u < n + 1, 2 log G <_ -3 n log 2 + 4 log ( n + 1 ) - 2 log ( 2 n + 1 ); "
                     "then 2 ( n + 1 ) ^ 2 <_ ( n + 2 ) ( 2 n + 1 ), e ^ x >_ x ^ 2 / 2 at x = ( n + 2 ) / 16, log 2 >_ 56 / 81 (z5dlog2), "
                     "log 2 < 253 / 365 and e < 3 give log G + u <_ log 60.")
    a = ante('z5dgnum')
    st = mkst(w, a)
    B = BCL(); T = '( 2 ^ N )'; T4 = '( 4 ^ N )'; q = '( ( N + 1 ) / C )'; q0 = '( ( N + 1 ) / %s )' % B
    A2 = '( ( 2 x. N ) + 1 )'; NN1 = '( N x. ( N + 1 ) )'
    G2U2 = '( ( G ^ 2 ) x. ( U ^ 2 ) )'; TQ = '( %s x. ( %s ^ 2 ) )' % (T, q0)
    h1 = st([], 'simp1', '( N e. ( ZZ>= ` 4 ) /\\ ( U e. RR /\\ N <_ U /\\ U < ( N + 1 ) ) )')
    h2 = st([], 'simp2', '( ( G e. RR /\\ 0 <_ G ) /\\ ( C e. RR /\\ %s <_ C ) )' % B)
    hm = st([], 'simp3', '%s <_ ( %s x. ( %s ^ 2 ) )' % (G2U2, T, q))
    nu = st([h1], 'simpld', 'N e. ( ZZ>= ` 4 )')
    uu = st([h1], 'simprd', '( U e. RR /\\ N <_ U /\\ U < ( N + 1 ) )')
    ur = st([uu], 'simp1d', 'U e. RR'); nU = st([uu], 'simp2d', 'N <_ U'); Ul = st([uu], 'simp3d', 'U < ( N + 1 )')
    gg = st([h2], 'simpld', '( G e. RR /\\ 0 <_ G )'); cc_ = st([h2], 'simprd', '( C e. RR /\\ %s <_ C )' % B)
    gr = st([gg], 'simpld', 'G e. RR'); g0 = st([gg], 'simprd', '0 <_ G')
    cr = st([cc_], 'simpld', 'C e. RR'); cB = st([cc_], 'simprd', '%s <_ C' % B)
    nn = sy(w, a, st([a1(w, a, w.s([], '4nn', '4 e. NN'), '4 e. NN'), nu], 'jca', '( 4 e. NN /\\ N e. ( ZZ>= ` 4 ) )'), 'eluznn', 'N e. NN')
    nr = st([nn], 'nnred', 'N e. RR'); nz = st([nn], 'nnzd', 'N e. ZZ'); n1_ = st([nn], 'nnge1d', '1 <_ N')
    two = a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')
    trp = st([two, nz], 'rpexpcld', '%s e. RR+' % T)
    four = rpl(w, a, '4')
    t4rp = st([four, nz], 'rpexpcld', '%s e. RR+' % T4)
    cl = Closure(w, a, {'N': [('NN', nn), ('RR', nr)]})
    a2rp = cl.mem(A2, 'RR+'); nn1rp = cl.mem(NN1, 'RR+'); n1rp = cl.mem('( N + 1 )', 'RR+')
    n1r = st([n1rp], 'rpred', '( N + 1 ) e. RR'); n10 = st([n1rp], 'rpge0d', '0 <_ ( N + 1 )')
    brp = st([st([t4rp, a2rp], 'rpmulcld', '( %s x. %s ) e. RR+' % (T4, A2)), nn1rp], 'rpdivcld', '%s e. RR+' % B)
    br = st([brp], 'rpred', '%s e. RR' % B)
    c0_ = st([st([], '0red', '0 e. RR'), br, cr, st([brp], 'rpgt0d', '0 < %s' % B), cB], 'ltletrd', '0 < C')
    crp = st([cr, c0_], 'elrpd', 'C e. RR+')
    # q <_ q0, hence G ^ 2 U ^ 2 <_ T q0 ^ 2
    qle = st([brp, crp, n1r, n10, cB], 'lediv2ad', '%s <_ %s' % (q, q0))
    qr = st([n1r, crp], 'rerpdivcld', '%s e. RR' % q)
    q0rp = st([n1rp, brp], 'rpdivcld', '%s e. RR+' % q0)
    q0r = st([q0rp], 'rpred', '%s e. RR' % q0)
    q2 = st([st([qr, st([n1r, crp, n10], 'divge0d', '0 <_ %s' % q)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (q, q)),
             st([q0r, qle], 'jca', '( %s e. RR /\\ %s <_ %s )' % (q0, q, q0)), w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (q, q0))
    tr = st([trp], 'rpred', '%s e. RR' % T)
    tq = st([st([qr], 'resqcld', '( %s ^ 2 ) e. RR' % q), st([q0r], 'resqcld', '( %s ^ 2 ) e. RR' % q0), tr, st([trp], 'rpge0d', '0 <_ %s' % T), q2],
            'lemul2ad', '( %s x. ( %s ^ 2 ) ) <_ %s' % (T, q, TQ))
    hm2 = st([st([st([gr], 'resqcld', '( G ^ 2 ) e. RR'), st([ur], 'resqcld', '( U ^ 2 ) e. RR')], 'remulcld', '%s e. RR' % G2U2),
              st([tr, st([qr], 'resqcld', '( %s ^ 2 ) e. RR' % q)], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (T, q)),
              st([tr, st([q0r], 'resqcld', '( %s ^ 2 ) e. RR' % q0)], 'remulcld', '%s e. RR' % TQ), hm, tq], 'letrd', '%s <_ %s' % (G2U2, TQ))
    GOAL = 'G <_ %s' % E60('U')
    # G = 0
    c0 = '( %s /\\ G = 0 )' % a
    s0 = mkst(w, c0)
    nu0 = s0([lift(w, ur, c0)], 'renegcld', '-u U e. RR')
    ep = sy(w, c0, nu0, 'efgt0', '0 < ( exp ` -u U )')
    EN = '( exp ` -u U )'
    rhs0 = lin.linarith(w, c0, [ep], '0 <_ %s' % E60('U'), leaves={EN: ('RR', s0([nu0], 'reefcld', '%s e. RR' % EN))}, atoms=[EN])
    g_0 = s0([s0([], 'simpr', 'G = 0'), rhs0], 'eqbrtrd', GOAL)
    # G > 0: logarithms
    c1 = '( %s /\\ -. G = 0 )' % a
    s1 = mkst(w, c1)
    L = lambda x: lift(w, x, c1)
    gpos = s1([s1([L(g0), s1([s1([], 'simpr', '-. G = 0')], 'neqned', 'G =/= 0')], 'jca', '( 0 <_ G /\\ G =/= 0 )'),
               s1([s1([], '0red', '0 e. RR'), L(gr), w.inst('ltlen')], 'syl2anc', '( 0 < G <-> ( 0 <_ G /\\ G =/= 0 ) )')], 'mpbird', '0 < G')
    grp = s1([L(gr), gpos], 'elrpd', 'G e. RR+')
    upos = lin.linarith(w, c1, [L(nU), L(n1_)], '0 < U', leaves={'N': ('RR', L(nr)), 'U': ('RR', L(ur))})
    urp = s1([L(ur), upos], 'elrpd', 'U e. RR+')
    nrp = s1([L(nn)], 'nnrpd', 'N e. RR+')
    twoz = a1(w, c1, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')
    two1 = L(two)
    lg = '( log ` G )'; lu = '( log ` U )'; ln_ = '( log ` N )'; ln1 = '( log ` ( N + 1 ) )'; la = '( log ` %s )' % A2
    ln2 = '( log ` ( N + 2 ) )'; l2 = '( log ` 2 )'; l3 = '( log ` 3 )'; l60 = '( log ` ; 6 0 )'
    lT = '( log ` %s )' % T; lT4 = '( log ` %s )' % T4; lB = '( log ` %s )' % B; lq = '( log ` %s )' % q0
    rps = {}

    def reg(X, stp):
        rps[X] = stp
        return stp

    def logexp(xrp, X, k, kz):
        return s1([xrp, kz, w.inst('relogexp')], 'syl2anc', '( log ` ( %s ^ %s ) ) = ( %s x. ( log ` %s ) )' % (X, k, k, X))
    reg('G', grp); reg('U', urp); reg('N', nrp); reg('2', two1); reg('( N + 1 )', L(n1rp)); reg(A2, L(a2rp)); reg(B, L(brp)); reg(q0, L(q0rp))
    reg(T, L(trp)); reg(T4, L(t4rp)); reg(NN1, L(nn1rp))
    # H1: 2 log G + 2 log U <_ log T + 2 log q0
    g2rp = reg('( G ^ 2 )', s1([grp, twoz], 'rpexpcld', '( G ^ 2 ) e. RR+')); u2rp = reg('( U ^ 2 )', s1([urp, twoz], 'rpexpcld', '( U ^ 2 ) e. RR+'))
    q02rp = reg('( %s ^ 2 )' % q0, s1([L(q0rp), twoz], 'rpexpcld', '( %s ^ 2 ) e. RR+' % q0))
    lhsrp = reg(G2U2, s1([g2rp, u2rp], 'rpmulcld', '%s e. RR+' % G2U2)); rhsrp = reg(TQ, s1([L(trp), q02rp], 'rpmulcld', '%s e. RR+' % TQ))
    lle = s1([L(hm2), s1([lhsrp, rhsrp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (G2U2, TQ, G2U2, TQ))], 'mpbid',
             '( log ` %s ) <_ ( log ` %s )' % (G2U2, TQ))
    e1 = s1([g2rp, u2rp], 'relogmuld', '( log ` %s ) = ( ( log ` ( G ^ 2 ) ) + ( log ` ( U ^ 2 ) ) )' % G2U2)
    e2 = logexp(grp, 'G', '2', twoz); e3 = logexp(urp, 'U', '2', twoz)
    e4 = s1([L(trp), q02rp], 'relogmuld', '( log ` %s ) = ( %s + ( log ` ( %s ^ 2 ) ) )' % (TQ, lT, q0))
    e5 = logexp(L(q0rp), q0, '2', twoz)
    # H2, H3: log 2 ^ N, log 4 ^ N
    e6 = logexp(two1, '2', 'N', L(nz))
    e7 = logexp(L(four), '4', 'N', L(nz))
    sq2r = a1(w, c1, w.s([w.s([], 'sq2', '( 2 ^ 2 ) = 4')], 'eqcomi', '4 = ( 2 ^ 2 )'), '4 = ( 2 ^ 2 )')
    l4 = s1([s1([sq2r], 'fveq2d', '( log ` 4 ) = ( log ` ( 2 ^ 2 ) )'), logexp(two1, '2', '2', twoz)], 'eqtrd', '( log ` 4 ) = ( 2 x. %s )' % l2)
    e7b = s1([e7, s1([l4], 'oveq2d', '( N x. ( log ` 4 ) ) = ( N x. ( 2 x. %s ) )' % l2)], 'eqtrd', '%s = ( N x. ( 2 x. %s ) )' % (lT4, l2))
    # H4, H5
    e8 = s1([L(n1rp), L(brp)], 'relogdivd', '%s = ( %s - %s )' % (lq, ln1, lB))
    TA = '( %s x. %s )' % (T4, A2)
    tarp = reg(TA, s1([L(t4rp), L(a2rp)], 'rpmulcld', '%s e. RR+' % TA))
    e9 = s1([tarp, L(nn1rp)], 'relogdivd', '%s = ( ( log ` %s ) - ( log ` %s ) )' % (lB, TA, NN1))
    e10 = s1([L(t4rp), L(a2rp)], 'relogmuld', '( log ` %s ) = ( %s + %s )' % (TA, lT4, la))
    e11 = s1([nrp, L(n1rp)], 'relogmuld', '( log ` %s ) = ( %s + %s )' % (NN1, ln_, ln1))
    # H6
    h6 = s1([L(nU), s1([nrp, urp, w.inst('logleb')], 'syl2anc', '( N <_ U <-> %s <_ %s )' % (ln_, lu))], 'mpbid', '%s <_ %s' % (ln_, lu))
    # H7: 2 ( N + 1 ) ^ 2 <_ ( N + 2 ) ( 2 N + 1 )
    n2rp = reg('( N + 2 )', s1([nrp, two1], 'rpaddcld', '( N + 2 ) e. RR+'))
    cl1 = Closure(w, c1, {'N': [('RR', L(nr))]})
    x7 = '( 2 x. ( ( N + 1 ) ^ 2 ) )'; y7 = '( ( N + 2 ) x. %s )' % A2
    pl = lin.linarith(w, c1, [L(n1_)], '%s <_ %s' % (x7, y7), closure=cl1, products=True)
    n12rp = reg('( ( N + 1 ) ^ 2 )', s1([L(n1rp), twoz], 'rpexpcld', '( ( N + 1 ) ^ 2 ) e. RR+'))
    x7rp = reg(x7, s1([two1, n12rp], 'rpmulcld', '%s e. RR+' % x7))
    y7rp = reg(y7, s1([n2rp, L(a2rp)], 'rpmulcld', '%s e. RR+' % y7))
    h7a = s1([pl, s1([x7rp, y7rp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (x7, y7, x7, y7))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (x7, y7))
    e12 = s1([two1, n12rp], 'relogmuld', '( log ` %s ) = ( %s + ( log ` ( ( N + 1 ) ^ 2 ) ) )' % (x7, l2))
    e13 = logexp(L(n1rp), '( N + 1 )', '2', twoz)
    e14 = s1([n2rp, L(a2rp)], 'relogmuld', '( log ` %s ) = ( %s + %s )' % (y7, ln2, la))
    # H8: at x = ( N + 2 ) / 16, x ^ 2 / 2 <_ e ^ x
    X = '( ( N + 2 ) / ; 1 6 )'
    sixt = reg('; 1 6', rpl(w, c1, '; 1 6'))
    xrp = reg(X, s1([n2rp, sixt], 'rpdivcld', '%s e. RR+' % X))
    xr = s1([xrp], 'rpred', '%s e. RR' % X)
    EX = '( exp ` %s )' % X
    eg = s1([xr, s1([xrp], 'rpge0d', '0 <_ %s' % X), w.inst('efge1p2')], 'syl2anc', '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ %s' % (X, X, EX))
    X2 = '( ( %s ^ 2 ) / 2 )' % X
    xsq = reg('( %s ^ 2 )' % X, s1([xrp, twoz], 'rpexpcld', '( %s ^ 2 ) e. RR+' % X))
    x2rp = reg(X2, s1([xsq, two1], 'rpdivcld', '%s e. RR+' % X2))
    clx = Closure(w, c1, {X: ('RR', xr), EX: ('RR', s1([xr], 'reefcld', '%s e. RR' % EX)), X2: ('RR', s1([x2rp], 'rpred', '%s e. RR' % X2))})
    for at in (X, EX, X2):
        clx.atom(at)
    eg2 = lin.linarith(w, c1, [eg, s1([xrp], 'rpge0d', '0 <_ %s' % X)], '%s <_ %s' % (X2, EX), closure=clx)
    erp = s1([xr], 'rpefcld', '%s e. RR+' % EX)
    h8a = s1([eg2, s1([x2rp, erp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (X2, EX, X2, EX))], 'mpbid',
             '( log ` %s ) <_ ( log ` %s )' % (X2, EX))
    h8b = s1([h8a, sy(w, c1, xr, 'relogef', '( log ` %s ) = %s' % (EX, X))], 'breqtrd', '( log ` %s ) <_ %s' % (X2, X))
    e15 = s1([xsq, two1], 'relogdivd', '( log ` %s ) = ( ( log ` ( %s ^ 2 ) ) - %s )' % (X2, X, l2))
    e16 = logexp(xrp, X, '2', twoz)
    e17 = s1([n2rp, sixt], 'relogdivd', '( log ` %s ) = ( %s - ( log ` ; 1 6 ) )' % (X, ln2))
    s16 = a1(w, c1, w.s([w.s([], '2exp4', '( 2 ^ 4 ) = ; 1 6')], 'eqcomi', '; 1 6 = ( 2 ^ 4 )'), '; 1 6 = ( 2 ^ 4 )')
    fourz = a1(w, c1, w.s([], '4z', '4 e. ZZ'), '4 e. ZZ')
    l16 = s1([s1([s16], 'fveq2d', '( log ` ; 1 6 ) = ( log ` ( 2 ^ 4 ) )'), logexp(two1, '2', '4', fourz)], 'eqtrd', '( log ` ; 1 6 ) = ( 4 x. %s )' % l2)
    # H9: ( 56 / 81 ) N <_ N log 2
    n0_ = s1([L(nr), lin.linarith(w, c1, [L(n1_)], '0 <_ N', closure=cl1)], 'jca', '( N e. RR /\\ 0 <_ N )')
    h9 = s1([a1(w, c1, num.real(w, '( ; 5 6 / ; 8 1 )'), '( ; 5 6 / ; 8 1 ) e. RR'), s1([two1], 'relogcld', '%s e. RR' % l2), L(nr), s1([n0_], 'simprd', '0 <_ N'),
             a1(w, c1, w.s([], 'z5dlog2', STATEMENTS['z5dlog2']), STATEMENTS['z5dlog2'])], 'lemul2ad', '( N x. ( ; 5 6 / ; 8 1 ) ) <_ ( N x. %s )' % l2)
    # H11
    h11 = a1(w, c1, w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % l2), '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % l2)
    # H12, H13: log 54 <_ log 60, 1 <_ log 3
    three = reg('3', rpl(w, c1, '3'))
    elt3 = a1(w, c1, w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')
    erp_ = a1(w, c1, w.s([], 'epr', '_e e. RR+'), '_e e. RR+')
    ele3 = s1([s1([erp_], 'rpred', '_e e. RR'), a1(w, c1, w.s([], '3re', '3 e. RR'), '3 e. RR'), elt3], 'ltled', '_e <_ 3')
    le3 = s1([ele3, s1([erp_, three, w.inst('logleb')], 'syl2anc', '( _e <_ 3 <-> ( log ` _e ) <_ %s )' % l3)], 'mpbid', '( log ` _e ) <_ %s' % l3)
    h13 = s1([a1(w, c1, w.s([], 'loge', '( log ` _e ) = 1'), '( log ` _e ) = 1'), le3], 'eqbrtrrd', '1 <_ %s' % l3)
    F54 = '( 2 x. ( 3 ^ 3 ) )'
    t27 = a1(w, c1, w.s([], '3exp3', '( 3 ^ 3 ) = ; 2 7'), '( 3 ^ 3 ) = ; 2 7')
    m54 = s1([s1([t27], 'oveq2d', '%s = ( 2 x. ; 2 7 )' % F54), a1(w, c1, num.mul_nat(w, 2, 27), '( 2 x. ; 2 7 ) = ; 5 4')], 'eqtrd', '%s = ; 5 4' % F54)
    le54 = s1([m54, a1(w, c1, num.le_lit(w, '; 5 4', '; 6 0'), '; 5 4 <_ ; 6 0')], 'eqbrtrd', '%s <_ ; 6 0' % F54)
    threez = a1(w, c1, w.s([], '3z', '3 e. ZZ'), '3 e. ZZ')
    t3rp = reg('( 3 ^ 3 )', s1([three, threez], 'rpexpcld', '( 3 ^ 3 ) e. RR+'))
    f54rp = reg(F54, s1([two1, t3rp], 'rpmulcld', '%s e. RR+' % F54))
    sixty = reg('; 6 0', rpl(w, c1, '; 6 0'))
    h12a = s1([le54, s1([f54rp, sixty, w.inst('logleb')], 'syl2anc', '( %s <_ ; 6 0 <-> ( log ` %s ) <_ %s )' % (F54, F54, l60))], 'mpbid', '( log ` %s ) <_ %s' % (F54, l60))
    e18 = s1([two1, t3rp], 'relogmuld', '( log ` %s ) = ( %s + ( log ` ( 3 ^ 3 ) ) )' % (F54, l2))
    e19 = logexp(three, '3', '3', threez)
    # the linear core (z5dglin): rewrite each bound into the atoms
    def rstep(stp, rules):
        """rewrite both sides of stp: ( c1 -> X R Y ) with rules"""
        f = cn(w, stp)
        from lin import parse_rel
        X_, rel, Y_ = parse_rel(f)
        ex_, nx = rwall(w, c1, X_, rules); ey_, ny = rwall(w, c1, Y_, rules)
        if ex_ is None:
            ex_ = s1([], 'eqidd', '%s = %s' % (X_, X_))
        if ey_ is None:
            ey_ = s1([], 'eqidd', '%s = %s' % (Y_, Y_))
        return s1([stp, ex_, ey_], '3brtr3d', '%s %s %s' % (nx, rel, ny))
    R = {'( log ` %s )' % G2U2: ('( ( log ` ( G ^ 2 ) ) + ( log ` ( U ^ 2 ) ) )', e1), '( log ` ( G ^ 2 ) )': ('( 2 x. %s )' % lg, e2),
         '( log ` ( U ^ 2 ) )': ('( 2 x. %s )' % lu, e3), '( log ` %s )' % TQ: ('( %s + ( log ` ( %s ^ 2 ) ) )' % (lT, q0), e4),
         '( log ` ( %s ^ 2 ) )' % q0: ('( 2 x. %s )' % lq, e5), lT: ('( N x. %s )' % l2, e6), lq: ('( %s - %s )' % (ln1, lB), e8),
         lB: ('( ( log ` %s ) - ( log ` %s ) )' % (TA, NN1), e9), '( log ` %s )' % TA: ('( %s + %s )' % (lT4, la), e10),
         lT4: ('( N x. ( 2 x. %s ) )' % l2, e7b), '( log ` %s )' % NN1: ('( %s + %s )' % (ln_, ln1), e11),
         '( log ` %s )' % x7: ('( %s + ( log ` ( ( N + 1 ) ^ 2 ) ) )' % l2, e12), '( log ` ( ( N + 1 ) ^ 2 ) )': ('( 2 x. %s )' % ln1, e13),
         '( log ` %s )' % y7: ('( %s + %s )' % (ln2, la), e14), '( log ` %s )' % X2: ('( ( log ` ( %s ^ 2 ) ) - %s )' % (X, l2), e15),
         '( log ` ( %s ^ 2 ) )' % X: ('( 2 x. ( log ` %s ) )' % X, e16), '( log ` %s )' % X: ('( %s - ( log ` ; 1 6 ) )' % ln2, e17),
         '( log ` ; 1 6 )': ('( 4 x. %s )' % l2, l16), '( log ` %s )' % F54: ('( %s + ( log ` ( 3 ^ 3 ) ) )' % l2, e18),
         '( log ` ( 3 ^ 3 ) )': ('( 3 x. %s )' % l3, e19)}
    r1 = rstep(lle, R); r3 = rstep(h7a, R); r4 = rstep(h8b, R); r8 = rstep(h12a, R)
    reals = [s1([grp], 'relogcld', '%s e. RR' % lg), s1([urp], 'relogcld', '%s e. RR' % lu), s1([nrp], 'relogcld', '%s e. RR' % ln_),
             s1([L(n1rp)], 'relogcld', '%s e. RR' % ln1), s1([L(a2rp)], 'relogcld', '%s e. RR' % la), s1([n2rp], 'relogcld', '%s e. RR' % ln2),
             s1([two1], 'relogcld', '%s e. RR' % l2), s1([three], 'relogcld', '%s e. RR' % l3), s1([sixty], 'relogcld', '%s e. RR' % l60), L(nr), L(ur)]
    fin = w.s([r1, h6, r3, r4, h9, L(Ul), h11, r8, h13, s1([n0_], 'simprd', '0 <_ N')] + reals, 'z5dglin', '( %s -> ( %s + U ) <_ %s )' % (c1, lg, l60))
    # exponentiate
    lgr = s1([grp], 'relogcld', '%s e. RR' % lg)
    ex = s1([fin, s1([s1([lgr, L(ur)], 'readdcld', '( %s + U ) e. RR' % lg), s1([sixty], 'relogcld', '%s e. RR' % l60), w.inst('efle')], 'syl2anc',
                     '( ( %s + U ) <_ %s <-> ( exp ` ( %s + U ) ) <_ ( exp ` %s ) )' % (lg, l60, lg, l60))], 'mpbid', '( exp ` ( %s + U ) ) <_ ( exp ` %s )' % (lg, l60))
    ea = s1([s1([lgr], 'recnd', '%s e. CC' % lg), s1([L(ur)], 'recnd', 'U e. CC'), w.inst('efadd')], 'syl2anc', '( exp ` ( %s + U ) ) = ( ( exp ` %s ) x. ( exp ` U ) )' % (lg, lg))
    eg_ = sy(w, c1, grp, 'reeflog', '( exp ` %s ) = G' % lg)
    ea2 = s1([ea, s1([eg_], 'oveq1d', '( ( exp ` %s ) x. ( exp ` U ) ) = ( G x. ( exp ` U ) )' % lg)], 'eqtrd', '( exp ` ( %s + U ) ) = ( G x. ( exp ` U ) )' % lg)
    e60 = sy(w, c1, sixty, 'reeflog', '( exp ` %s ) = ; 6 0' % l60)
    gle = s1([ea2, ex, e60], '3brtr3d', '( G x. ( exp ` U ) ) <_ ; 6 0')
    eurp = s1([L(ur)], 'rpefcld', '( exp ` U ) e. RR+')
    gle2 = s1([gle, s1([L(gr), a1(w, c1, num.real(w, '; 6 0'), '; 6 0 e. RR'), eurp], 'lemuldivd', '( ( G x. ( exp ` U ) ) <_ ; 6 0 <-> G <_ ( ; 6 0 / ( exp ` U ) ) )')],
              'mpbid', 'G <_ ( ; 6 0 / ( exp ` U ) )')
    en = sy(w, c1, s1([L(ur)], 'recnd', 'U e. CC'), 'efneg', '( exp ` -u U ) = ( 1 / ( exp ` U ) )')
    dv = s1([a1(w, c1, num.cc(w, '; 6 0'), '; 6 0 e. CC'), s1([eurp], 'rpcnd', '( exp ` U ) e. CC'), s1([eurp], 'rpne0d', '( exp ` U ) =/= 0')], 'divrecd',
            '( ; 6 0 / ( exp ` U ) ) = ( ; 6 0 x. ( 1 / ( exp ` U ) ) )')
    rh = s1([dv, s1([en], 'oveq2d', '%s = ( ; 6 0 x. ( 1 / ( exp ` U ) ) )' % E60('U'))], 'eqtr4d', '( ; 6 0 / ( exp ` U ) ) = %s' % E60('U'))
    g_1 = s1([gle2, rh], 'breqtrd', GOAL)
    w.qed([g_0, g_1], 'pm2.61dan', STATEMENTS['z5dgnum'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        if os.environ.get('Z5D_WRITE_ONLY'):
            w.write()
        else:
            run(w)
