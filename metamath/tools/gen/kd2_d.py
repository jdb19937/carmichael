"""Sortie KD2: the tails (kd2vmp, kd2npf, kd2pwt, kd2sub).  MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_d.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd2lib import *
from cl import formula_of, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, nlinarith
from mvlib import ringeq, ringeqp
import num

only = sys.argv[1:]


def vmcong(w, x, y, U):
    """closed ( x = y -> VMT(x) = VMT(y) )"""
    H = '%s = %s' % (x, y)
    a = w.s([], 'fveq2', '( %s -> ( Lam ` %s ) = ( Lam ` %s ) )' % (H, x, y))
    b = w.s([], 'oveq1', '( %s -> ( %s ^c -u ( 1 + %s ) ) = ( %s ^c -u ( 1 + %s ) ) )' % (H, x, U, y, U))
    return w.s([a, b], 'oveq12d', '( %s -> %s = %s )' % (H, VMT(x, U), VMT(y, U)))


def vmfacts(w, Ah, k, kn, ur):
    """( Ah -> VMT(k,U) e. RR ), ( Ah -> 0 <_ VMT(k,U) ) with kn : ( Ah -> k e. NN ), ur : ( Ah -> U e. RR )"""
    d = lambda ref, h, c: D(w, Ah, ref, h, c)
    U = formula_of(w, ur).split(' -> ')[1].split(' e. ')[0]
    lm = d('syl', [kn, w.inst('vmacl')], '( Lam ` %s ) e. RR' % k)
    lm0 = d('syl', [kn, w.inst('vmage0')], '0 <_ ( Lam ` %s )' % k)
    ex = d('renegcld', [d('readdcld', [a1(w, Ah, '1re', '1 e. RR'), ur], '( 1 + %s ) e. RR' % U)], '-u ( 1 + %s ) e. RR' % U)
    cx = d('rpcxpcld', [d('nnrpd', [kn], '%s e. RR+' % k), ex], '( %s ^c -u ( 1 + %s ) ) e. RR+' % (k, U))
    r = d('remulcld', [lm, d('rpred', [cx], '( %s ^c -u ( 1 + %s ) ) e. RR' % (k, U))], '%s e. RR' % VMT(k, U))
    z = d('mulge0d', [lm, d('rpred', [cx], '( %s ^c -u ( 1 + %s ) ) e. RR' % (k, U)), lm0, d('rpge0d', [cx], '0 <_ ( %s ^c -u ( 1 + %s ) )' % (k, U))], '0 <_ %s' % VMT(k, U))
    return r, z


def gen_vmp():
    w = W('kd2vmp', 'A finite sum of ` Lam ( k ) k^-(1+U) ` over ` A C_ NN ` is at most ~ vmsharp ` ( 5 / 4 ) / U + 5 ` ( ~ isumless , ~ vmsercvg ).')
    A0 = S['kd2vmp'].split(' -> sum_')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simpl', [], '( U e. RR+ /\\ U <_ 1 )'); g2 = d('simpr', [], '( A e. Fin /\\ A C_ NN )')
    up = d('simpld', [g1], 'U e. RR+'); ur = d('rpred', [up], 'U e. RR')
    af = d('simpld', [g2], 'A e. Fin'); ass = d('simprd', [g2], 'A C_ NN')
    Fn = '( n e. NN |-> %s )' % VMT('n', 'U')
    t = d('readdcld', [a1(w, A0, '1re', '1 e. RR'), ur], '( 1 + U ) e. RR')
    t1 = d('ltaddrpd', [a1(w, A0, '1re', '1 e. RR'), up], '1 < ( 1 + U )')
    cv = d('syl2anc', [t, t1, w.inst('vmsercvg')], 'seq 1 ( + , %s ) e. dom ~~>' % Fn)
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    vr, v0 = vmfacts(w, Ak, 'k', kn, lift(w, ur, Ak))
    mc = w.s([vmcong(w, 'n', 'k', 'U')], 'adantl', '( ( %s /\\ n = k ) -> %s = %s )' % (Ak, VMT('n', 'U'), VMT('k', 'U')))
    fv = D(w, Ak, 'fvmptd', [a1(w, Ak, 'eqid', '%s = %s' % (Fn, Fn)), mc, kn, D(w, Ak, 'recnd', [vr], '%s e. CC' % VMT('k', 'U'))], '( %s ` k ) = %s' % (Fn, VMT('k', 'U')))
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    il = d('isumless', [nnu, a1(w, A0, '1z', '1 e. ZZ'), af, ass, fv, vr, v0, cv], 'sum_ k e. A %s <_ sum_ k e. NN %s' % (VMT('k', 'U'), VMT('k', 'U')))
    vs = d('syl', [g1, w.inst('vmsharp')], 'sum_ k e. NN %s <_ ( ( ( 5 / 4 ) / U ) + 5 )' % VMT('k', 'U'))
    isr = d('isumrecl', [nnu, a1(w, A0, '1z', '1 e. ZZ'), fv, vr, cv], 'sum_ k e. NN %s e. RR' % VMT('k', 'U'))
    fr = d('fsumrecl', [af, D(w, '( %s /\\ k e. A )' % A0, 'mpd', [w.s([], 'simpr', '( ( %s /\\ k e. A ) -> k e. A )' % A0), lift(w, d('ex' if False else 'idi', [], 'T.'), A0) if False else
                                                                  D(w, '( %s /\\ k e. A )' % A0, 'idi', [], 'T.')], 'T.') if False else
                        D(w, '( %s /\\ k e. A )' % A0, 'idi', [], 'T.')], 'T.') if False else None
    Aa = '( %s /\\ k e. A )' % A0
    kna = D(w, Aa, 'sseldd', [lift(w, ass, Aa), w.s([], 'simpr', '( %s -> k e. A )' % Aa)], 'k e. NN')
    vra, _ = vmfacts(w, Aa, 'k', kna, lift(w, ur, Aa))
    fr = d('fsumrecl', [af, vra], 'sum_ k e. A %s e. RR' % VMT('k', 'U'))
    cl = Closure(w, A0, {'U': ('RR+', up)})
    fin = d('letrd', [fr, isr, cl.mem('( ( ( 5 / 4 ) / U ) + 5 )', 'RR'), il, vs], 'sum_ k e. A %s <_ ( ( ( 5 / 4 ) / U ) + 5 )' % VMT('k', 'U'))
    w.qed([fin], 'idi', S['kd2vmp'])
    return only_run(w, only)

def BN(x): return 'if ( %s e. Prime , 0 , ( ( Lam ` %s ) x. ( %s ^c -u ( 3 / 4 ) ) ) )' % (x, x, x)


def ifle0(w, A, phi, Y, y0, yr):
    """( A -> if ( phi , 0 , Y ) <_ Y ) from y0 : ( ( A /\\ phi ) -> 0 <_ Y ), yr : ( ( A /\\ -. phi ) -> Y e. RR )"""
    IF = 'if ( %s , 0 , %s )' % (phi, Y)
    h1 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (IF, Y, IF, Y))
    h2 = w.s([], 'breq1', '( %s = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (Y, IF, Y, Y, IF, Y))
    An = '( %s /\\ -. %s )' % (A, phi)
    h4 = D(w, An, 'leidd', [yr], '%s <_ %s' % (Y, Y))
    return w.s([h1, h2, y0, h4], 'ifbothda', '( %s -> %s <_ %s )' % (A, IF, Y))


def gen_npf():
    w = W('kd2npf', 'Lean ` KDerivDetect.tsum_nonprime_vonMangoldt_rpow_le ` (partial sums): ` sum_ n <_ M , n not prime Lam ( n ) n^(-3/4) <_ 20 ` (Lean ` 150 ` ): ~ fsumvma2 , ` sum_ k >_ 2 p^(-3k/4) <_ ( 5 / 2 ) p^(-3/2) ` ( ` p^(-3/4) <_ 3 / 5 ` ), ~ kd2vmp at ` U = 1 / 2 ` .')
    A0 = 'M e. RR'
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    mr = w.s([], 'id', '( M e. RR -> M e. RR )')
    FL = '( 1 ... ( |_ ` M ) )'; PP = '( ( 0 [,] M ) i^i Prime )'
    LR = '( ( log ` M ) / ( log ` p ) )'; Lf = '( |_ ` %s )' % LR; JJ = '( 1 ... %s )' % Lf
    PJ = '( p ^ j )'
    # fsumvma2
    H = 'n = %s' % PJ
    e1 = w.s([], 'eleq1', '( %s -> ( n e. Prime <-> %s e. Prime ) )' % (H, PJ))
    e2 = w.s([w.s([], 'fveq2', '( %s -> ( Lam ` n ) = ( Lam ` %s ) )' % (H, PJ)), w.s([], 'oveq1', '( %s -> ( n ^c -u ( 3 / 4 ) ) = ( %s ^c -u ( 3 / 4 ) ) )' % (H, PJ))],
             'oveq12d', '( %s -> ( ( Lam ` n ) x. ( n ^c -u ( 3 / 4 ) ) ) = ( ( Lam ` %s ) x. ( %s ^c -u ( 3 / 4 ) ) ) )' % (H, PJ, PJ))
    hb = w.s([e1, w.s([], 'eqidd', '( %s -> 0 = 0 )' % H), e2], 'ifbieq12d', '( %s -> %s = %s )' % (H, BN('n'), BN(PJ)))
    An = '( %s /\\ n e. %s )' % (A0, FL)
    nn_ = D(w, An, 'syl', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FL)), w.inst('elfznn')], 'n e. NN')
    m34 = w.s([num.real(w, '( 3 / 4 )')], 'a1i', '( %s -> ( 3 / 4 ) e. RR )' % An)
    Yn = '( ( Lam ` n ) x. ( n ^c -u ( 3 / 4 ) ) )'
    ynr = D(w, An, 'remulcld', [D(w, An, 'syl', [nn_, w.inst('vmacl')], '( Lam ` n ) e. RR'), D(w, An, 'rpred', [D(w, An, 'rpcxpcld', [D(w, An, 'nnrpd', [nn_], 'n e. RR+'), D(w, An, 'renegcld', [m34], '-u ( 3 / 4 ) e. RR')], '( n ^c -u ( 3 / 4 ) ) e. RR+')], '( n ^c -u ( 3 / 4 ) ) e. RR')], '%s e. RR' % Yn)
    bnr = D(w, An, 'ifcld', [a1(w, An, '0re', '0 e. RR'), ynr], '%s e. RR' % BN('n'))
    bnc = D(w, An, 'recnd', [bnr], '%s e. CC' % BN('n'))
    Az = '( %s /\\ ( n e. %s /\\ ( Lam ` n ) = 0 ) )' % (A0, FL)
    lz = w.s([], 'simprr', '( %s -> ( Lam ` n ) = 0 )' % Az)
    nnz = D(w, Az, 'syl', [w.s([], 'simprl', '( %s -> n e. %s )' % (Az, FL)), w.inst('elfznn')], 'n e. NN')
    cxz = D(w, Az, 'cxpcld', [D(w, Az, 'nncnd', [nnz], 'n e. CC'), D(w, Az, 'negcld', [w.s([num.cc(w, '( 3 / 4 )')], 'a1i', '( %s -> ( 3 / 4 ) e. CC )' % Az)], '-u ( 3 / 4 ) e. CC')], '( n ^c -u ( 3 / 4 ) ) e. CC')
    y0 = D(w, Az, 'eqtrd', [D(w, Az, 'oveq1d', [lz], '%s = ( 0 x. ( n ^c -u ( 3 / 4 ) ) )' % Yn), D(w, Az, 'mul02d', [cxz], '( 0 x. ( n ^c -u ( 3 / 4 ) ) ) = 0')], '%s = 0' % Yn)
    bz = D(w, Az, 'eqtrd', [D(w, Az, 'ifeq2d', [y0], '%s = if ( n e. Prime , 0 , 0 )' % BN('n')), a1(w, Az, 'ifid', 'if ( n e. Prime , 0 , 0 ) = 0')], '%s = 0' % BN('n'))
    vma = d('fsumvma2', [hb, mr, bnc, bz], 'sum_ n e. %s %s = sum_ p e. %s sum_ j e. %s %s' % (FL, BN('n'), PP, JJ, BN(PJ)))
    # ---- inner bound under Ap
    Ap = '( %s /\\ p e. %s )' % (A0, PP)
    dp = lambda ref, h, c: D(w, Ap, ref, h, c)
    ppp = w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PP))
    pr_ = dp('syl', [ppp, w.inst('elinel2')], 'p e. Prime'); pic = dp('syl', [ppp, w.inst('elinel1')], 'p e. ( 0 [,] M )')
    pnn = dp('syl', [pr_, w.inst('prmnn')], 'p e. NN'); prp = dp('nnrpd', [pnn], 'p e. RR+'); prr = dp('nnred', [pnn], 'p e. RR'); pc = dp('nncnd', [pnn], 'p e. CC')
    p2 = dp('syl', [dp('syl', [pr_, w.inst('prmuz2')], 'p e. ( ZZ>= ` 2 )'), w.inst('eluzle')], '2 <_ p')
    mrp = lift(w, mr, Ap)
    pm = dp('simp3d', [dp('mpbid', [pic, dp('syl2anc', [a1(w, Ap, '0re', '0 e. RR'), mrp, w.inst('elicc2')], '( p e. ( 0 [,] M ) <-> ( p e. RR /\\ 0 <_ p /\\ p <_ M ) )')],
                                  '( p e. RR /\\ 0 <_ p /\\ p <_ M )')], 'p <_ M')
    clp = Closure(w, Ap, {'p': ('RR', prr), 'M': ('RR', mrp)})
    mrpp = dp('elrpd', [mrp, linarith(w, Ap, [p2, pm], '0 < M', closure=clp)], 'M e. RR+')
    p1 = linarith(w, Ap, [p2], '1 < p', closure=clp)
    lpp = dp('elrpd', [dp('relogcld', [prp], '( log ` p ) e. RR'), dp('mpbird', [p1, dp('syl', [prp, w.inst('loggt0b')], '( 0 < ( log ` p ) <-> 1 < p )')], '0 < ( log ` p )')], '( log ` p ) e. RR+')
    llm = dp('mpbid', [pm, dp('logled', [prp, mrpp], '( p <_ M <-> ( log ` p ) <_ ( log ` M ) )')], '( log ` p ) <_ ( log ` M )')
    lmr = dp('relogcld', [mrpp], '( log ` M ) e. RR')
    l1 = dp('mpbid', [dp('eqbrtrd', [dp('mullidd', [dp('rpcnd', [lpp], '( log ` p ) e. CC')], '( 1 x. ( log ` p ) ) = ( log ` p )'), llm], '( 1 x. ( log ` p ) ) <_ ( log ` M )'),
                      dp('lemuldivd', [a1(w, Ap, '1re', '1 e. RR'), lmr, lpp], '( ( 1 x. ( log ` p ) ) <_ ( log ` M ) <-> 1 <_ %s )' % LR)], '1 <_ %s' % LR)
    lrr = dp('rerpdivcld', [lmr, lpp], '%s e. RR' % LR)
    lfn = dp('syl2anc', [lrr, l1, w.inst('flge1nn')], '%s e. NN' % Lf)
    R = '( p ^c -u ( 3 / 4 ) )'; SS = '( p ^c -u ( 1 + ( 1 / 2 ) ) )'
    m34p = w.s([num.real(w, '( 3 / 4 )')], 'a1i', '( %s -> ( 3 / 4 ) e. RR )' % Ap)
    rrp = dp('rpcxpcld', [prp, dp('renegcld', [m34p], '-u ( 3 / 4 ) e. RR')], '%s e. RR+' % R)
    ssp = dp('rpcxpcld', [prp, dp('renegcld', [dp('readdcld', [a1(w, Ap, '1re', '1 e. RR'), w.s([num.real(w, '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % Ap)], '( 1 + ( 1 / 2 ) ) e. RR')],
                                                  '-u ( 1 + ( 1 / 2 ) ) e. RR')], '%s e. RR+' % SS)
    pn0 = dp('nnne0d', [pnn], 'p =/= 0')
    c34 = dp('negcld', [w.s([num.cc(w, '( 3 / 4 )')], 'a1i', '( %s -> ( 3 / 4 ) e. CC )' % Ap)], '-u ( 3 / 4 ) e. CC')
    c32 = dp('negcld', [dp('recnd', [dp('readdcld', [a1(w, Ap, '1re', '1 e. RR'), w.s([num.real(w, '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % Ap)], '( 1 + ( 1 / 2 ) ) e. RR')], '( 1 + ( 1 / 2 ) ) e. CC')], '-u ( 1 + ( 1 / 2 ) ) e. CC')
    # r^2 = SS
    rsq = dp('sqvald', [dp('rpcnd', [rrp], '%s e. CC' % R)], '( %s ^ 2 ) = ( %s x. %s )' % (R, R, R))
    ra = dp('cxpaddd', [pc, pn0, c34, c34], '( p ^c ( -u ( 3 / 4 ) + -u ( 3 / 4 ) ) ) = ( %s x. %s )' % (R, R))
    ex1 = ringeq(w, Ap, '( -u ( 3 / 4 ) + -u ( 3 / 4 ) )', '-u ( 1 + ( 1 / 2 ) )', Closure(w, Ap, {}))
    rb = dp('oveq2d', [ex1], '( p ^c ( -u ( 3 / 4 ) + -u ( 3 / 4 ) ) ) = %s' % SS)
    r2s = dp('eqtr3d', [dp('eqtr4d', [rsq, ra], '( %s ^ 2 ) = ( p ^c ( -u ( 3 / 4 ) + -u ( 3 / 4 ) ) )' % R), rb] if False else [rsq, dp('eqtr3d', [ra, rb], '( %s x. %s ) = %s' % (R, R, SS))], 'T.') if False else \
        dp('eqtrd', [rsq, dp('eqtr3d', [ra, rb], '( %s x. %s ) = %s' % (R, R, SS))], '( %s ^ 2 ) = %s' % (R, SS))
    # SS^2 = 1 / p^3 <_ 1 / 8
    ssq = dp('sqvald', [dp('rpcnd', [ssp], '%s e. CC' % SS)], '( %s ^ 2 ) = ( %s x. %s )' % (SS, SS, SS))
    sa = dp('cxpaddd', [pc, pn0, c32, c32], '( p ^c ( -u ( 1 + ( 1 / 2 ) ) + -u ( 1 + ( 1 / 2 ) ) ) ) = ( %s x. %s )' % (SS, SS))
    ex2 = ringeq(w, Ap, '( -u ( 1 + ( 1 / 2 ) ) + -u ( 1 + ( 1 / 2 ) ) )', '-u 3', Closure(w, Ap, {}))
    sb = dp('oveq2d', [ex2], '( p ^c ( -u ( 1 + ( 1 / 2 ) ) + -u ( 1 + ( 1 / 2 ) ) ) ) = ( p ^c -u 3 )')
    sc_ = dp('cxpnegd', [pc, pn0, a1(w, Ap, '3cn', '3 e. CC')], '( p ^c -u 3 ) = ( 1 / ( p ^c 3 ) )')
    sd = dp('oveq2d', [dp('syl2anc', [pc, a1(w, Ap, '3nn0', '3 e. NN0'), w.inst('cxpexp')], '( p ^c 3 ) = ( p ^ 3 )')], '( 1 / ( p ^c 3 ) ) = ( 1 / ( p ^ 3 ) )')
    s2 = chain(w, Ap, ['( %s ^ 2 )' % SS, '( %s x. %s )' % (SS, SS), '( p ^c ( -u ( 1 + ( 1 / 2 ) ) + -u ( 1 + ( 1 / 2 ) ) ) )', '( p ^c -u 3 )', '( 1 / ( p ^c 3 ) )', '( 1 / ( p ^ 3 ) )'],
               [ssq, ('r', sa), sb, sc_, sd])
    p3 = dp('eqbrtrrd', [a1(w, Ap, 'cu2', '( 2 ^ 3 ) = 8'), dp('leexp1ad', [a1(w, Ap, '2re', '2 e. RR'), prr, a1(w, Ap, '3nn0', '3 e. NN0'), a1(w, Ap, '0le2', '0 <_ 2'), p2], '( 2 ^ 3 ) <_ ( p ^ 3 )')],
             '8 <_ ( p ^ 3 )')
    p3p = dp('rpexpcld', [prp, a1(w, Ap, '3z', '3 e. ZZ')], '( p ^ 3 ) e. RR+')
    i8 = dp('lediv2ad', [w.s([num.rp(w, '8')], 'a1i', '( %s -> 8 e. RR+ )' % Ap), p3p, a1(w, Ap, '1re', '1 e. RR'), a1(w, Ap, '0le1', '0 <_ 1'), p3], '( 1 / ( p ^ 3 ) ) <_ ( 1 / 8 )')
    N925 = '( 9 / ; 2 5 )'; N35 = '( 3 / 5 )'
    q1 = w.s([w.s([num.cc(w, N925)], 'sqvali', '( %s ^ 2 ) = ( %s x. %s )' % (N925, N925, N925)), num.mul_lits(w, N925, N925)], 'eqtri', '( %s ^ 2 ) = ( ; 8 1 / ; ; 6 2 5 )' % N925)
    q2 = w.s([num.le_lit(w, '( 1 / 8 )', '( ; 8 1 / ; ; 6 2 5 )'), q1], 'breqtrri', '( 1 / 8 ) <_ ( %s ^ 2 )' % N925)
    clq = Closure(w, Ap, {})
    s2l = dp('letrd', [dp('rerpdivcld', [a1(w, Ap, '1re', '1 e. RR'), p3p], '( 1 / ( p ^ 3 ) ) e. RR'), clq.mem('( 1 / 8 )', 'RR'), clq.mem('( %s ^ 2 )' % N925, 'RR'), i8, w.s([q2], 'a1i', '( %s -> ( 1 / 8 ) <_ ( %s ^ 2 ) )' % (Ap, N925))],
              '( 1 / ( p ^ 3 ) ) <_ ( %s ^ 2 )' % N925)
    s2b = dp('eqbrtrd', [s2, s2l], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (SS, N925))
    ssr = dp('rpred', [ssp], '%s e. RR' % SS)
    sle = dp('mpbird', [s2b, dp('le2sqd', [ssr, clq.mem(N925, 'RR'), dp('rpge0d', [ssp], '0 <_ %s' % SS), clq.ge0(N925)], '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (SS, N925, SS, N925))],
              '%s <_ %s' % (SS, N925))
    q3 = w.s([w.s([num.cc(w, N35)], 'sqvali', '( %s ^ 2 ) = ( %s x. %s )' % (N35, N35, N35)), num.mul_lits(w, N35, N35)], 'eqtri', '( %s ^ 2 ) = %s' % (N35, N925))
    r2b = dp('breqtrrd', [dp('eqbrtrd', [r2s, sle], '( %s ^ 2 ) <_ %s' % (R, N925)), w.s([q3], 'a1i', '( %s -> ( %s ^ 2 ) = %s )' % (Ap, N35, N925))], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (R, N35))
    rr_ = dp('rpred', [rrp], '%s e. RR' % R)
    rle = dp('mpbird', [r2b, dp('le2sqd', [rr_, clq.mem(N35, 'RR'), dp('rpge0d', [rrp], '0 <_ %s' % R), clq.ge0(N35)], '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (R, N35, R, N35))], '%s <_ %s' % (R, N35))
    # geometric sum over ( 2 ... Lf )
    lfz = dp('nnzd', [lfn], '%s e. ZZ' % Lf)
    RC = dp('rpcnd', [rrp], '%s e. CC' % R)
    r1 = dp('ltned', [rr_, dp('ltletrd' if False else 'lelttrd', [rr_, clq.mem(N35, 'RR'), a1(w, Ap, '1re', '1 e. RR'), rle, w.s([num.le_lit(w, N35, '1', strict=True)], 'a1i', '( %s -> %s < 1 )' % (Ap, N35))], '%s < 1' % R)], '%s =/= 1' % R)
    rlt1 = dp('lelttrd', [rr_, clq.mem(N35, 'RR'), a1(w, Ap, '1re', '1 e. RR'), rle, w.s([num.le_lit(w, N35, '1', strict=True)], 'a1i', '( %s -> %s < 1 )' % (Ap, N35))], '%s < 1' % R)
    LF1 = '( %s + 1 )' % Lf
    lf1z = dp('peano2zd', [lfz], '%s e. ZZ' % LF1)
    u2 = dp('sylibr', [dp('3jca', [a1(w, Ap, '2z', '2 e. ZZ'), lf1z, linarith(w, Ap, [dp('nnge1d', [lfn], '1 <_ %s' % Lf)], '2 <_ %s' % LF1, closure=Closure(w, Ap, {Lf: ('RR', dp('zred', [lfz], '%s e. RR' % Lf))}))],
                           '( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s )' % (LF1, LF1)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (LF1, LF1, LF1))],
             '%s e. ( ZZ>= ` 2 )' % LF1)
    geo = dp('geoserg', [RC, r1, a1(w, Ap, '2nn0', '2 e. NN0'), u2], 'sum_ j e. ( 2 ..^ %s ) ( %s ^ j ) = ( ( ( %s ^ 2 ) - ( %s ^ %s ) ) / ( 1 - %s ) )' % (LF1, R, R, R, LF1, R))
    fz3 = dp('syl', [lfz, w.inst('fzval3')], '( 2 ... %s ) = ( 2 ..^ %s )' % (Lf, LF1))
    g0 = dp('sumeq1d', [fz3], 'sum_ j e. ( 2 ... %s ) ( %s ^ j ) = sum_ j e. ( 2 ..^ %s ) ( %s ^ j )' % (Lf, R, LF1, R))
    GS = 'sum_ j e. ( 2 ... %s ) ( %s ^ j )' % (Lf, R)
    gg = dp('eqtrd', [g0, geo], '%s = ( ( ( %s ^ 2 ) - ( %s ^ %s ) ) / ( 1 - %s ) )' % (GS, R, R, LF1, R))
    omr = dp('elrpd', [dp('resubcld', [a1(w, Ap, '1re', '1 e. RR'), rr_], '( 1 - %s ) e. RR' % R), dp('posdifd' if False else 'syl', [rlt1, dp('idi' if False else 'syl2anc', [rr_, a1(w, Ap, '1re', '1 e. RR'), w.inst('posdif')], '( %s < 1 <-> 0 < ( 1 - %s ) )' % (R, R))] if False else
                                                                                               [dp('syl2anc', [rr_, a1(w, Ap, '1re', '1 e. RR'), w.inst('posdif')], '( %s < 1 <-> 0 < ( 1 - %s ) )' % (R, R))], 'T.') if False else
                  dp('mpbid', [rlt1, dp('syl2anc', [rr_, a1(w, Ap, '1re', '1 e. RR'), w.inst('posdif')], '( %s < 1 <-> 0 < ( 1 - %s ) )' % (R, R))], '0 < ( 1 - %s )' % R)], '( 1 - %s ) e. RR+' % R)
    R2 = '( %s ^ 2 )' % R; RL = '( %s ^ %s )' % (R, LF1)
    r2r = dp('reexpcld', [rr_, a1(w, Ap, '2nn0', '2 e. NN0')], '%s e. RR' % R2)
    rlr = dp('reexpcld', [rr_, dp('nnnn0d', [dp('peano2nnd', [lfn], '%s e. NN' % LF1)], '%s e. NN0' % LF1)], '%s e. RR' % RL)
    rl0 = dp('expge0d', [rr_, dp('nnnn0d', [dp('peano2nnd', [lfn], '%s e. NN' % LF1)], '%s e. NN0' % LF1), dp('rpge0d', [rrp], '0 <_ %s' % R)], '0 <_ %s' % RL)
    cg = Closure(w, Ap, {R2: ('RR', r2r), RL: ('RR', rlr)}); cg.atom(R2); cg.atom(RL)
    ga = dp('lediv1dd', [cg.mem('( %s - %s )' % (R2, RL), 'RR'), r2r, omr, linarith(w, Ap, [rl0], '( %s - %s ) <_ %s' % (R2, RL, R2), closure=cg)],
            '( ( %s - %s ) / ( 1 - %s ) ) <_ ( %s / ( 1 - %s ) )' % (R2, RL, R, R2, R))
    cg2 = Closure(w, Ap, {R2: ('RR', r2r), R: ('RR', rr_)}); cg2.atom(R2); cg2.atom(R)
    r20 = dp('sqge0d', [rr_], '0 <_ %s' % R2)
    gb0 = nlinarith(w, Ap, [rle, r20], '%s <_ ( ( 1 - %s ) x. ( ( 5 / 2 ) x. %s ) )' % (R2, R, R2), closure=cg2)
    gb = dp('mpbird', [gb0, dp('ledivmuld', [r2r, cg2.mem('( ( 5 / 2 ) x. %s )' % R2, 'RR'), omr], '( ( %s / ( 1 - %s ) ) <_ ( ( 5 / 2 ) x. %s ) <-> %s <_ ( ( 1 - %s ) x. ( ( 5 / 2 ) x. %s ) ) )' % (R2, R, R2, R2, R, R2))],
             '( %s / ( 1 - %s ) ) <_ ( ( 5 / 2 ) x. %s )' % (R2, R, R2))
    gsum = dp('letrd', [dp('rerpdivcld', [cg.mem('( %s - %s )' % (R2, RL), 'RR'), omr], '( ( %s - %s ) / ( 1 - %s ) ) e. RR' % (R2, RL, R)), dp('rerpdivcld', [r2r, omr], '( %s / ( 1 - %s ) ) e. RR' % (R2, R)),
                        cg2.mem('( ( 5 / 2 ) x. %s )' % R2, 'RR'), ga, gb], '( ( %s - %s ) / ( 1 - %s ) ) <_ ( ( 5 / 2 ) x. %s )' % (R2, RL, R, R2))
    gsb = dp('eqbrtrd', [gg, gsum], '%s <_ ( ( 5 / 2 ) x. %s )' % (GS, R2))
    # h ( j )
    LP = '( log ` p )'
    hj = lambda j: 'if ( %s = 1 , 0 , ( %s x. ( %s ^ %s ) ) )' % (j, LP, R, j)
    Aj = '( %s /\\ j e. %s )' % (Ap, JJ)
    dj = lambda ref, h, c: D(w, Aj, ref, h, c)
    jJ = w.s([], 'simpr', '( %s -> j e. %s )' % (Aj, JJ))
    jnn = dj('syl', [jJ, w.inst('elfznn')], 'j e. NN')
    L = lambda st: lift(w, st, Aj)
    Y = '( ( Lam ` %s ) x. ( %s ^c -u ( 3 / 4 ) ) )' % (PJ, PJ)
    # C <_ h : case j = 1
    A1j = '( %s /\\ j = 1 )' % Aj
    j1 = w.s([], 'simpr', '( %s -> j = 1 )' % A1j)
    pj1 = D(w, A1j, 'eqtrd', [D(w, A1j, 'oveq2d', [j1], '%s = ( p ^ 1 )' % PJ), D(w, A1j, 'exp1d', [lift(w, pc, A1j)], '( p ^ 1 ) = p')], '%s = p' % PJ)
    pjp = D(w, A1j, 'eqeltrd', [pj1, lift(w, pr_, A1j)], '%s e. Prime' % PJ)
    c0 = D(w, A1j, 'syl', [pjp, w.inst('iftrue')], '%s = 0' % BN(PJ))
    h0 = D(w, A1j, 'syl', [j1, w.inst('iftrue')], '%s = 0' % hj('j'))
    ch1 = D(w, A1j, 'eqled' if False else 'eqled', [D(w, A1j, 'eqeltrd', [c0, a1(w, A1j, '0re', '0 e. RR')], '%s e. RR' % BN(PJ)), D(w, A1j, 'eqtr4d', [c0, h0], '%s = %s' % (BN(PJ), hj('j')))], '%s <_ %s' % (BN(PJ), hj('j')))
    # case j =/= 1
    A2j = '( %s /\\ -. j = 1 )' % Aj
    jn2 = w.s([], 'simpr', '( %s -> -. j = 1 )' % A2j)
    hy = D(w, A2j, 'syl', [jn2, w.inst('iffalse')], '%s = ( %s x. ( %s ^ j ) )' % (hj('j'), LP, R))
    jnn2 = lift(w, jnn, A2j)
    vp = D(w, A2j, 'syl2anc', [lift(w, pr_, A2j), jnn2, w.inst('vmappw')], '( Lam ` %s ) = %s' % (PJ, LP))
    pcj = lift(w, pc, A2j); jn0 = D(w, A2j, 'nnnn0d', [jnn2], 'j e. NN0')
    ce1 = D(w, A2j, 'syl2anc', [pcj, jn0, w.inst('cxpexp')], '( p ^c j ) = %s' % PJ)
    ce2 = D(w, A2j, 'cxpmuld', [lift(w, prp, A2j), D(w, A2j, 'nnred', [jnn2], 'j e. RR'), lift(w, c34, A2j)], '( p ^c ( j x. -u ( 3 / 4 ) ) ) = ( ( p ^c j ) ^c -u ( 3 / 4 ) )')
    ce3 = D(w, A2j, 'oveq2d', [D(w, A2j, 'mulcomd', [D(w, A2j, 'nncnd', [jnn2], 'j e. CC'), lift(w, c34, A2j)], '( j x. -u ( 3 / 4 ) ) = ( -u ( 3 / 4 ) x. j )')],
            '( p ^c ( j x. -u ( 3 / 4 ) ) ) = ( p ^c ( -u ( 3 / 4 ) x. j ) )')
    ce4 = D(w, A2j, 'cxpmul2d', [pcj, lift(w, c34, A2j), jn0], '( p ^c ( -u ( 3 / 4 ) x. j ) ) = ( %s ^ j )' % R)
    ce5 = D(w, A2j, 'oveq1d', [ce1], '( ( p ^c j ) ^c -u ( 3 / 4 ) ) = ( %s ^c -u ( 3 / 4 ) )' % PJ)
    cee = chain(w, A2j, ['( %s ^c -u ( 3 / 4 ) )' % PJ, '( ( p ^c j ) ^c -u ( 3 / 4 ) )', '( p ^c ( j x. -u ( 3 / 4 ) ) )', '( p ^c ( -u ( 3 / 4 ) x. j ) )', '( %s ^ j )' % R],
                [('r', ce5), ('r', ce2), ce3, ce4])
    ye = D(w, A2j, 'oveq12d', [vp, cee], '%s = ( %s x. ( %s ^ j ) )' % (Y, LP, R))
    lpr2 = lift(w, dp('rpred', [lpp], '%s e. RR' % LP), A2j)
    yr2 = D(w, A2j, 'eqeltrd', [ye, D(w, A2j, 'remulcld', [lpr2, D(w, A2j, 'reexpcld', [lift(w, rr_, A2j), jn0], '( %s ^ j ) e. RR' % R)], '( %s x. ( %s ^ j ) ) e. RR' % (LP, R))], '%s e. RR' % Y)
    Ajy = '( %s /\\ %s e. Prime )' % (A2j, PJ)
    y0_ = D(w, Ajy, 'breqtrrd', [D(w, Ajy, 'mulge0d', [lift(w, lpr2, Ajy), D(w, Ajy, 'reexpcld', [lift(w, rr_, Ajy), lift(w, jn0, Ajy)], '( %s ^ j ) e. RR' % R),
                                                       lift(w, dp('rpge0d', [lpp], '0 <_ %s' % LP), Ajy), D(w, Ajy, 'expge0d', [lift(w, rr_, Ajy), lift(w, jn0, Ajy), lift(w, dp('rpge0d', [rrp], '0 <_ %s' % R), Ajy)], '0 <_ ( %s ^ j )' % R)],
                                     '0 <_ ( %s x. ( %s ^ j ) )' % (LP, R)), lift(w, ye, Ajy)], '0 <_ %s' % Y)
    Ajn = '( %s /\\ -. %s e. Prime )' % (A2j, PJ)
    il = ifle0(w, A2j, '%s e. Prime' % PJ, Y, y0_, lift(w, yr2, Ajn))
    ch2 = D(w, A2j, 'breqtrrd', [D(w, A2j, 'breqtrd', [il, ye], '%s <_ ( %s x. ( %s ^ j ) )' % (BN(PJ), LP, R)), hy], '%s <_ %s' % (BN(PJ), hj('j')))
    chh = D(w, Aj, 'pm2.61dan', [ch1, ch2], '%s <_ %s' % (BN(PJ), hj('j')))
    # sums over JJ
    Ah2 = '( %s /\\ j e. ( 2 ... %s ) )' % (Ap, Lf)
    def bnr_(Ah, x, xnn):
        dd = lambda ref, h, c: D(w, Ah, ref, h, c)
        y = dd('remulcld', [dd('syl', [xnn, w.inst('vmacl')], '( Lam ` %s ) e. RR' % x), dd('rpred', [dd('rpcxpcld', [dd('nnrpd', [xnn], '%s e. RR+' % x), dd('renegcld', [w.s([num.real(w, '( 3 / 4 )')], 'a1i', '( %s -> ( 3 / 4 ) e. RR )' % Ah)], '-u ( 3 / 4 ) e. RR')],
                                                                                                                '( %s ^c -u ( 3 / 4 ) ) e. RR+' % x)], '( %s ^c -u ( 3 / 4 ) ) e. RR' % x)],
               '( ( Lam ` %s ) x. ( %s ^c -u ( 3 / 4 ) ) ) e. RR' % (x, x))
        return dd('ifcld', [a1(w, Ah, '0re', '0 e. RR'), y], '%s e. RR' % BN(x))
    pjn = dj('nnexpcld', [lift(w, pnn, Aj), dj('nnnn0d', [jnn], 'j e. NN0')], '%s e. NN' % PJ)
    cr_ = bnr_(Aj, PJ, pjn)
    def hr_(Ah, jj):
        dd = lambda ref, h, c: D(w, Ah, ref, h, c)
        jn0 = dd('nnnn0d', [dd('syl', [jj, w.inst('elfznn')], 'j e. NN')], 'j e. NN0') if 'JJ' else None
        return dd('ifcld', [a1(w, Ah, '0re', '0 e. RR'), dd('remulcld', [lift(w, dp('rpred', [lpp], '%s e. RR' % LP), Ah), dd('reexpcld', [lift(w, rr_, Ah), jn0], '( %s ^ j ) e. RR' % R)],
                                                                    '( %s x. ( %s ^ j ) ) e. RR' % (LP, R))], '%s e. RR' % hj('j'))
    hr = hr_(Aj, jJ)
    jf = dp('fzfid', [], '%s e. Fin' % JJ)
    s1 = dp('fsumle', [jf, cr_, hr, chh], 'sum_ j e. %s %s <_ sum_ j e. %s %s' % (JJ, BN(PJ), JJ, hj('j')))
    # fsum1p
    lfu = dp('sylib' if False else 'mpbi' if False else 'syl', [lfn, w.inst('elnnuz') if False else w.inst('nnuz') if False else w.inst('elnnuz')], '%s e. ( ZZ>= ` 1 )' % Lf) if False else \
        dp('mpbid', [lfn, a1(w, Ap, 'elnnuz', '( %s e. NN <-> %s e. ( ZZ>= ` 1 ) )' % (Lf, Lf))], '%s e. ( ZZ>= ` 1 )' % Lf)
    hc = D(w, Aj, 'recnd', [hr], '%s e. CC' % hj('j'))
    hq = w.s([w.s([], 'eqeq1', '( j = 1 -> ( j = 1 <-> 1 = 1 ) )'), w.s([], 'eqidd', '( j = 1 -> 0 = 0 )'),
              w.s([w.s([], 'oveq2', '( j = 1 -> ( %s ^ j ) = ( %s ^ 1 ) )' % (R, R))], 'oveq2d', '( j = 1 -> ( %s x. ( %s ^ j ) ) = ( %s x. ( %s ^ 1 ) ) )' % (LP, R, LP, R))],
             'ifbieq12d', '( j = 1 -> %s = %s )' % (hj('j'), hj('1')))
    f1p = dp('fsum1p', [lfu, hc, hq], 'sum_ j e. %s %s = ( %s + sum_ j e. ( ( 1 + 1 ) ... %s ) %s )' % (JJ, hj('j'), hj('1'), Lf, hj('j')))
    h1z = w.s([w.s([w.s([], 'eqid', '1 = 1'), w.inst('iftrue')], 'ax-mp', '%s = 0' % hj('1'))], 'a1i', '( %s -> %s = 0 )' % (Ap, hj('1')))
    f12 = dp('sumeq1d', [dp('oveq1d', [a1(w, Ap, '1p1e2', '( 1 + 1 ) = 2')], '( ( 1 + 1 ) ... %s ) = ( 2 ... %s )' % (Lf, Lf))],
             'sum_ j e. ( ( 1 + 1 ) ... %s ) %s = sum_ j e. ( 2 ... %s ) %s' % (Lf, hj('j'), Lf, hj('j')))
    j2in = w.s([], 'simpr', '( %s -> j e. ( 2 ... %s ) )' % (Ah2, Lf))
    j2le = D(w, Ah2, 'syl', [j2in, w.inst('elfzle1')], '2 <_ j')
    j2z = D(w, Ah2, 'syl', [j2in, w.inst('elfzelz')], 'j e. ZZ')
    jn1 = D(w, Ah2, 'mpbir' if False else 'syl', [D(w, Ah2, 'gtned' if False else 'ltned' if False else 'idi', [], 'T.') if False else None], 'T.') if False else None
    cl2j = Closure(w, Ah2, {'j': ('RR', D(w, Ah2, 'zred', [j2z], 'j e. RR'))})
    j1lt = linarith(w, Ah2, [j2le], '1 < j', closure=cl2j)
    jne = D(w, Ah2, 'gtned', [a1(w, Ah2, '1re', '1 e. RR'), j1lt], 'j =/= 1')
    jne2 = D(w, Ah2, 'neneqd', [jne], '-. j = 1')
    hy2 = D(w, Ah2, 'syl', [jne2, w.inst('iffalse')], '%s = ( %s x. ( %s ^ j ) )' % (hj('j'), LP, R))
    f2s = dp('sumeq2dv', [hy2], 'sum_ j e. ( 2 ... %s ) %s = sum_ j e. ( 2 ... %s ) ( %s x. ( %s ^ j ) )' % (Lf, hj('j'), Lf, LP, R))
    j2n0 = D(w, Ah2, 'nnnn0d', [D(w, Ah2, 'syl', [D(w, Ah2, 'syl', [j2in, w.inst('elfzuz')], 'j e. ( ZZ>= ` 2 )'), w.inst('uz2m1nn') if False else w.inst('eluz2nn')], 'j e. NN')], 'j e. NN0')
    rjc = D(w, Ah2, 'expcld', [lift(w, RC, Ah2), j2n0], '( %s ^ j ) e. CC' % R)
    fmc = dp('fsummulc2', [dp('fzfid', [], '( 2 ... %s ) e. Fin' % Lf), dp('rpcnd', [lpp], '%s e. CC' % LP), rjc], '( %s x. %s ) = sum_ j e. ( 2 ... %s ) ( %s x. ( %s ^ j ) )' % (LP, GS, Lf, LP, R))
    HS = 'sum_ j e. %s %s' % (JJ, hj('j'))
    hsum = chain(w, Ap, [HS, '( %s + sum_ j e. ( ( 1 + 1 ) ... %s ) %s )' % (hj('1'), Lf, hj('j')), '( 0 + sum_ j e. ( 2 ... %s ) %s )' % (Lf, hj('j')),
                         'sum_ j e. ( 2 ... %s ) %s' % (Lf, hj('j')), 'sum_ j e. ( 2 ... %s ) ( %s x. ( %s ^ j ) )' % (Lf, LP, R), '( %s x. %s )' % (LP, GS)],
                 [f1p, dp('oveq12d', [h1z, f12], '( %s + sum_ j e. ( ( 1 + 1 ) ... %s ) %s ) = ( 0 + sum_ j e. ( 2 ... %s ) %s )' % (hj('1'), Lf, hj('j'), Lf, hj('j'))),
                  dp('addlidd', [dp('fsumcl', [dp('fzfid', [], '( 2 ... %s ) e. Fin' % Lf), D(w, Ah2, 'recnd', [hr_(Ah2, D(w, Ah2, 'sseldd', [lift(w, dp('syl', [a1(w, Ap, '2eluzge1' if False else 'idi', 'T.') if False else
                                                                                                                                                           w.s([w.s([], '2eluzge1', '2 e. ( ZZ>= ` 1 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 1 ) )' % Ap), w.inst('fzss1')],
                                                                                                                                                          '( 2 ... %s ) C_ ( 1 ... %s )' % (Lf, Lf)), Ah2), j2in], 'j e. %s' % JJ))], '%s e. CC' % hj('j'))],
                                            'sum_ j e. ( 2 ... %s ) %s e. CC' % (Lf, hj('j')))], '( 0 + sum_ j e. ( 2 ... %s ) %s ) = sum_ j e. ( 2 ... %s ) %s' % (Lf, hj('j'), Lf, hj('j'))),
                  f2s, ('r', fmc)])
    lpr = dp('rpred', [lpp], '%s e. RR' % LP)
    gsr = dp('fsumrecl', [dp('fzfid', [], '( 2 ... %s ) e. Fin' % Lf), D(w, Ah2, 'reexpcld', [lift(w, rr_, Ah2), j2n0], '( %s ^ j ) e. RR' % R)], '%s e. RR' % GS)
    t1 = dp('lemul2ad', [gsr, cg2.mem('( ( 5 / 2 ) x. %s )' % R2, 'RR'), lpr, dp('rpge0d', [lpp], '0 <_ %s' % LP), gsb], '( %s x. %s ) <_ ( %s x. ( ( 5 / 2 ) x. %s ) )' % (LP, GS, LP, R2))
    VP = VMT('p', '( 1 / 2 )')
    vpe = dp('syl', [pr_, w.inst('vmaprm')], '( Lam ` p ) = %s' % LP)
    cl6 = Closure(w, Ap, {LP: ('CC', dp('rpcnd', [lpp], '%s e. CC' % LP)), SS: ('CC', dp('rpcnd', [ssp], '%s e. CC' % SS))}); cl6.atom(LP); cl6.atom(SS)
    t2 = dp('eqtrd', [dp('oveq2d', [dp('oveq2d', [r2s], '( ( 5 / 2 ) x. %s ) = ( ( 5 / 2 ) x. %s )' % (R2, SS))], '( %s x. ( ( 5 / 2 ) x. %s ) ) = ( %s x. ( ( 5 / 2 ) x. %s ) )' % (LP, R2, LP, SS)),
                      ringeq(w, Ap, '( %s x. ( ( 5 / 2 ) x. %s ) )' % (LP, SS), '( ( 5 / 2 ) x. ( %s x. %s ) )' % (LP, SS), cl6)], '( %s x. ( ( 5 / 2 ) x. %s ) ) = ( ( 5 / 2 ) x. ( %s x. %s ) )' % (LP, R2, LP, SS))
    t3 = dp('oveq2d', [dp('oveq1d', [vpe], '%s = ( %s x. %s )' % (VP, LP, SS))], '( ( 5 / 2 ) x. %s ) = ( ( 5 / 2 ) x. ( %s x. %s ) )' % (VP, LP, SS))
    CS = 'sum_ j e. %s %s' % (JJ, BN(PJ))
    inner = dp('breqtrrd', [dp('breqtrd', [dp('letrd', [dp('fsumrecl', [jf, cr_], '%s e. RR' % CS), dp('fsumrecl', [jf, hr], '%s e. RR' % HS), dp('remulcld', [lpr, gsr], '( %s x. %s ) e. RR' % (LP, GS)), s1,
                                                          dp('eqled', [dp('fsumrecl', [jf, hr], '%s e. RR' % HS), hsum], '%s <_ ( %s x. %s )' % (HS, LP, GS))], '%s <_ ( %s x. %s )' % (CS, LP, GS)) if False else
                                          dp('letrd', [dp('fsumrecl', [jf, cr_], '%s e. RR' % CS), dp('remulcld', [lpr, gsr], '( %s x. %s ) e. RR' % (LP, GS)),
                                                       dp('remulcld', [lpr, cg2.mem('( ( 5 / 2 ) x. %s )' % R2, 'RR')], '( %s x. ( ( 5 / 2 ) x. %s ) ) e. RR' % (LP, R2)),
                                                       dp('breqtrd', [s1, hsum], '%s <_ ( %s x. %s )' % (CS, LP, GS)), t1], '%s <_ ( %s x. ( ( 5 / 2 ) x. %s ) )' % (CS, LP, R2)), t2],
                               '%s <_ ( ( 5 / 2 ) x. ( %s x. %s ) )' % (CS, LP, SS)), t3], '%s <_ ( ( 5 / 2 ) x. %s )' % (CS, VP))
    # outer
    ppf = d('syl', [mr, w.inst('ppifi')], '%s e. Fin' % PP)
    csr = dp('fsumrecl', [jf, cr_], '%s e. RR' % CS)
    vpr = dp('remulcld', [w.s([num.real(w, '( 5 / 2 )')], 'a1i', '( %s -> ( 5 / 2 ) e. RR )' % Ap), vmfacts(w, Ap, 'p', pnn, w.s([num.real(w, '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % Ap))[0]],
              '( ( 5 / 2 ) x. %s ) e. RR' % VP)
    o1 = d('fsumle', [ppf, csr, vpr, inner], 'sum_ p e. %s %s <_ sum_ p e. %s ( ( 5 / 2 ) x. %s )' % (PP, CS, PP, VP))
    vpc = dp('recnd', [vmfacts(w, Ap, 'p', pnn, w.s([num.real(w, '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % Ap))[0]], '%s e. CC' % VP)
    o2 = d('fsummulc2', [ppf, w.s([num.cc(w, '( 5 / 2 )')], 'a1i', '( %s -> ( 5 / 2 ) e. CC )' % A0), vpc], '( ( 5 / 2 ) x. sum_ p e. %s %s ) = sum_ p e. %s ( ( 5 / 2 ) x. %s )' % (PP, VP, PP, VP))
    cb = w.s([vmcong(w, 'p', 'k', '( 1 / 2 )')], 'cbvsumv', 'sum_ p e. %s %s = sum_ k e. %s %s' % (PP, VP, PP, VMT('k', '( 1 / 2 )')))
    pss = d('sstrd', [a1(w, A0, 'inss2', '%s C_ Prime' % PP), a1(w, A0, 'prmssnn', 'Prime C_ NN')], '%s C_ NN' % PP)
    vm = use(w, A0, 'kd2vmp', {'U': '( 1 / 2 )', 'A': PP},
             d('jca', [d('jca', [w.s([num.rp(w, '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / 2 ) e. RR+ )' % A0), w.s([num.le_lit(w, '( 1 / 2 )', '1')], 'a1i', '( %s -> ( 1 / 2 ) <_ 1 )' % A0)],
                                '( ( 1 / 2 ) e. RR+ /\\ ( 1 / 2 ) <_ 1 )'), d('jca', [ppf, pss], '( %s e. Fin /\\ %s C_ NN )' % (PP, PP))],
               '( ( ( 1 / 2 ) e. RR+ /\\ ( 1 / 2 ) <_ 1 ) /\\ ( %s e. Fin /\\ %s C_ NN ) )' % (PP, PP)))
    VS = 'sum_ p e. %s %s' % (PP, VP)
    vm2 = d('eqbrtrd', [w.s([cb], 'a1i', '( %s -> %s = sum_ k e. %s %s )' % (A0, VS, PP, VMT('k', '( 1 / 2 )'))), vm], '%s <_ ( ( ( 5 / 4 ) / ( 1 / 2 ) ) + 5 )' % VS)
    vsr = d('fsumrecl', [ppf, vmfacts(w, Ap, 'p', pnn, w.s([num.real(w, '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % Ap))[0]], '%s e. RR' % VS)
    Q52 = '( ( 5 / 4 ) / ( 1 / 2 ) )'
    c54 = w.s([num.cc(w, '( 5 / 4 )')], 'a1i', '( %s -> ( 5 / 4 ) e. CC )' % A0)
    qd = d('divdiv2d', [c54, a1(w, A0, 'ax-1cn', '1 e. CC'), a1(w, A0, '2cn', '2 e. CC'), a1(w, A0, 'ax-1ne0', '1 =/= 0'), a1(w, A0, '2ne0', '2 =/= 0')],
           '%s = ( ( ( 5 / 4 ) x. 2 ) / 1 )' % Q52)
    m52 = d('mulcld', [c54, a1(w, A0, '2cn', '2 e. CC')], '( ( 5 / 4 ) x. 2 ) e. CC')
    qe = d('eqtrd', [qd, d('div1d', [m52], '( ( ( 5 / 4 ) x. 2 ) / 1 ) = ( ( 5 / 4 ) x. 2 )')], '%s = ( ( 5 / 4 ) x. 2 )' % Q52)
    q52r = d('eqeltrd', [qe, d('remulcld', [w.s([num.real(w, '( 5 / 4 )')], 'a1i', '( %s -> ( 5 / 4 ) e. RR )' % A0), a1(w, A0, '2re', '2 e. RR')], '( ( 5 / 4 ) x. 2 ) e. RR')], '%s e. RR' % Q52)
    clo = Closure(w, A0, {VS: ('RR', vsr), Q52: ('RR', q52r)})
    clo.atom(VS); clo.atom(Q52)
    o3 = linarith(w, A0, [vm2, qe], '( ( 5 / 2 ) x. %s ) <_ ; 2 0' % VS, closure=clo)
    OS = 'sum_ p e. %s %s' % (PP, CS)
    osr = d('fsumrecl', [ppf, csr], '%s e. RR' % OS)
    fin0 = d('letrd', [osr, clo.mem('( ( 5 / 2 ) x. %s )' % VS, 'RR'), a1(w, A0, None, None) if False else w.s([num.real(w, '; 2 0')], 'a1i', '( %s -> ; 2 0 e. RR )' % A0),
                       d('breqtrrd', [o1, o2], '%s <_ ( ( 5 / 2 ) x. %s )' % (OS, VS)), o3], '%s <_ ; 2 0' % OS)
    fin = d('eqbrtrd', [vma, fin0], 'sum_ n e. %s %s <_ ; 2 0' % (FL, BN('n')))
    w.qed([fin], 'idi', S['kd2npf'])
    return only_run(w, only)


def gen_pwt():
    w = W('kd2pwt', 'At a prime ` P ` the term of ` LSK ( j + 1 , s0 ) ` is the window weight ` ( log P )^(j+1) P^-eta ` times the window coefficient ` chi ( P ) log P P^(-1 - i T) ` (Lean ` hwin ` in ` norm_LSeries_sub_window_le ` ).')
    A0 = S['kd2pwt'].split(' -> ( ( ( ( log `')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    nxh = d('simp1', [], NXH); g2 = d('simp2', [], '( T e. RR /\\ E e. RR /\\ J e. NN0 )'); pp = d('simp3', [], 'P e. Prime')
    tr = d('simp1d', [g2], 'T e. RR'); er = d('simp2d', [g2], 'E e. RR'); jn = d('simp3d', [g2], 'J e. NN0')
    pnn = d('syl', [pp, w.inst('prmnn')], 'P e. NN'); pc = d('nncnd', [pnn], 'P e. CC'); pn0 = d('nnne0d', [pnn], 'P =/= 0')
    S0T = S0()
    MS = '-u %s' % S0T; ME = '-u E'; MT = '( -u 1 - ( T x. _i ) )'
    cl = Closure(w, A0, {'E': ('RR', er), 'T': ('RR', tr), '_i': ('CC', a1(w, A0, 'ax-icn', '_i e. CC'))})
    cl.atom('_i')
    ex = ringeq(w, A0, MS, '( %s + %s )' % (ME, MT), cl)
    c1 = d('oveq2d', [ex], '( P ^c %s ) = ( P ^c ( %s + %s ) )' % (MS, ME, MT))
    c2 = d('cxpaddd', [pc, pn0, cl.mem(ME, 'CC'), cl.mem(MT, 'CC')], '( P ^c ( %s + %s ) ) = ( ( P ^c %s ) x. ( P ^c %s ) )' % (ME, MT, ME, MT))
    vp = d('syl', [pp, w.inst('vmaprm')], '( Lam ` P ) = ( log ` P )')
    LK = '( ( log ` P ) ^ ( J + 1 ) )'
    lhs = LT('( J + 1 )', S0T, 'P')
    m1 = '( ( %s x. ( %s x. ( log ` P ) ) ) x. ( ( P ^c %s ) x. ( P ^c %s ) ) )' % (LK, CHV('P'), ME, MT)
    e1 = d('oveq12d', [d('oveq2d', [d('oveq2d', [vp], '( %s x. ( Lam ` P ) ) = ( %s x. ( log ` P ) )' % (CHV('P'), CHV('P')))],
                                '( %s x. ( %s x. ( Lam ` P ) ) ) = ( %s x. ( %s x. ( log ` P ) ) )' % (LK, CHV('P'), LK, CHV('P'))),
                       d('eqtrd', [c1, c2], '( P ^c %s ) = ( ( P ^c %s ) x. ( P ^c %s ) )' % (MS, ME, MT))], '%s = %s' % (lhs, m1))
    lg = d('recnd', [d('relogcld', [d('nnrpd', [pnn], 'P e. RR+')], '( log ` P ) e. RR')], '( log ` P ) e. CC')
    cl2 = Closure(w, A0, {LK: ('CC', d('expcld', [lg, d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')], '%s e. CC' % LK)), CHV('P'): ('CC', d('syl2anc', [nxh, pnn, w.inst('lchrcl')], '%s e. CC' % CHV('P'))),
                          '( log ` P )': ('CC', lg), '( P ^c %s )' % ME: ('CC', d('cxpcld', [pc, cl.mem(ME, 'CC')], '( P ^c %s ) e. CC' % ME)),
                          '( P ^c %s )' % MT: ('CC', d('cxpcld', [pc, cl.mem(MT, 'CC')], '( P ^c %s ) e. CC' % MT))})
    for a in (LK, CHV('P'), '( log ` P )', '( P ^c %s )' % ME, '( P ^c %s )' % MT):
        cl2.atom(a)
    e2 = ringeq(w, A0, m1, '( %s x. %s )' % (PHI('J', 'P'), CP('P')), cl2)
    fin = d('eqtrd', [e1, e2], '%s = ( %s x. %s )' % (lhs, PHI('J', 'P'), CP('P')))
    w.qed([fin], 'idi', S['kd2pwt'])
    return only_run(w, only)


def ifge0(w, A, phi, Y, y0):
    """( A -> 0 <_ if ( phi , 0 , Y ) ) from y0 : ( A -> 0 <_ Y )"""
    IF = 'if ( %s , 0 , %s )' % (phi, Y)
    h1 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IF, IF))
    h2 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (Y, IF, Y, IF))
    a1_ = w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( ( %s /\\ %s ) -> 0 <_ 0 )' % (A, phi))
    a2_ = w.s([y0], 'adantr', '( ( %s /\\ -. %s ) -> 0 <_ %s )' % (A, phi, Y))
    return w.s([h1, h2, a1_, a2_], 'ifbothda', '( %s -> 0 <_ %s )' % (A, IF))


def gen_pt():
    w = W('kd2pt', 'Pointwise majorant of the diagonal term off the window (Lean ` hpt ` in ` norm_LSeries_sub_window_le ` with ` tsum_nonprime_log_pow_le ` , ` tsum_low_log_pow_le ` , ` tsum_high_log_pow_le ` ): nonprime ` M ` via ~ kdlogpow at ` 1 / 4 ` , ` M <_ Y ` via ` log M <_ log Y ` , ` Z < M ` via ` M^(-eta/2) <_ Z^(-eta/2) ` .')
    A0 = S['kd2pt'].split(' -> ' + DT('M', 'K', 'E'))[0][2:]
    B0 = '( ( E e. RR+ /\\ K e. NN0 ) /\\ ( ( Y e. RR /\\ 1 <_ Y ) /\\ Z e. RR+ ) /\\ M e. NN )'
    d = lambda ref, h, c: D(w, B0, ref, h, c)
    g1 = d('simp1', [], '( E e. RR+ /\\ K e. NN0 )'); g2 = d('simp2', [], '( ( Y e. RR /\\ 1 <_ Y ) /\\ Z e. RR+ )'); mn = d('simp3', [], 'M e. NN')
    ep = d('simpld', [g1], 'E e. RR+'); kn = d('simprd', [g1], 'K e. NN0')
    gy = d('simpld', [g2], '( Y e. RR /\\ 1 <_ Y )'); zp = d('simprd', [g2], 'Z e. RR+')
    yr = d('simpld', [gy], 'Y e. RR'); y1 = d('simprd', [gy], '1 <_ Y')
    er = d('rpred', [ep], 'E e. RR')
    mr = d('nnred', [mn], 'M e. RR'); mrp = d('nnrpd', [mn], 'M e. RR+'); mc = d('nncnd', [mn], 'M e. CC'); m1 = d('nnge1d', [mn], '1 <_ M')
    lm = d('syl', [mn, w.inst('vmacl')], '( Lam ` M ) e. RR'); lm0 = d('syl', [mn, w.inst('vmage0')], '0 <_ ( Lam ` M )')
    lg = d('relogcld', [mrp], '( log ` M ) e. RR'); lg0 = d('logge0d', [mr, m1], '0 <_ ( log ` M )')
    LK = '( ( log ` M ) ^ K )'
    lk = d('reexpcld', [lg, kn], '%s e. RR' % LK); lk0 = d('expge0d', [lg, kn, lg0], '0 <_ %s' % LK)
    E2 = '( E / 2 )'
    cl = Closure(w, B0, {'E': ('RR+', ep), 'K': ('NN0', kn), 'M': ('NN', mn), 'Y': ('RR', yr), 'Z': ('RR+', zp)})
    def cx(ex):
        st = d('rpcxpcld', [mrp, cl.mem(ex, 'RR')], '( M ^c %s ) e. RR+' % ex)
        return st, d('rpred', [st], '( M ^c %s ) e. RR' % ex), d('rpge0d', [st], '0 <_ ( M ^c %s )' % ex)
    C1 = '( M ^c -u ( 1 + E ) )'
    c1p, c1r, c10 = cx('-u ( 1 + E )')
    LL = '( ( Lam ` M ) x. %s )' % LK
    llr = d('remulcld', [lm, lk], '%s e. RR' % LL); ll0 = d('mulge0d', [lm, lk, lm0, lk0], '0 <_ %s' % LL)
    DTM = DT('M', 'K', 'E')
    # the three majorant terms and their signs
    F4 = '( ( 4 ^ K ) x. ( ! ` K ) )'
    cl.leaf('( ! ` K )', 'RR+', d('nnrpd', [d('faccld', [kn], '( ! ` K ) e. NN')], '( ! ` K ) e. RR+'))
    f4r = cl.mem(F4, 'RR'); f40 = cl.ge0(F4)
    M34 = '( M ^c -u ( 3 / 4 ) )'
    m34p, m34r, m340 = cx('-u ( 3 / 4 )')
    Yb = '( ( Lam ` M ) x. %s )' % M34
    ybr = d('remulcld', [lm, m34r], '%s e. RR' % Yb); yb0 = d('mulge0d', [lm, m34r, lm0, m340], '0 <_ %s' % Yb)
    bnr = d('ifcld', [a1(w, B0, '0re', '0 e. RR'), ybr], '%s e. RR' % BN('M'))
    bn0 = ifge0(w, B0, 'M e. Prime', Yb, yb0)
    T1 = '( %s x. %s )' % (F4, BN('M'))
    t1r = d('remulcld', [f4r, bnr], '%s e. RR' % T1); t10 = d('mulge0d', [f4r, bnr, f40, bn0], '0 <_ %s' % T1)
    LY = '( ( log ` Y ) ^ K )'
    ly0 = d('expge0d', [d('relogcld', [cl.mem('Y', 'RR+') if False else d('elrpd', [yr, linarith(w, B0, [y1], '0 < Y', closure=Closure(w, B0, {'Y': ('RR', yr)}))], 'Y e. RR+')], '( log ` Y ) e. RR'),
                        kn, d('logge0d', [yr, y1], '0 <_ ( log ` Y )')], '0 <_ %s' % LY)
    ypp = d('elrpd', [yr, linarith(w, B0, [y1], '0 < Y', closure=Closure(w, B0, {'Y': ('RR', yr)}))], 'Y e. RR+')
    lyr = d('reexpcld', [d('relogcld', [ypp], '( log ` Y ) e. RR'), kn], '%s e. RR' % LY)
    VM = VMT('M', 'E')
    vmr = d('remulcld', [lm, c1r], '%s e. RR' % VM); vm0 = d('mulge0d', [lm, c1r, lm0, c10], '0 <_ %s' % VM)
    T2 = '( %s x. %s )' % (LY, VM)
    t2r = d('remulcld', [lyr, vmr], '%s e. RR' % T2); t20 = d('mulge0d', [lyr, vmr, ly0, vm0], '0 <_ %s' % T2)
    ZE = '( Z ^c -u %s )' % E2
    zep = d('rpcxpcld', [zp, cl.mem('-u %s' % E2, 'RR')], '%s e. RR+' % ZE)
    C3 = '( M ^c -u ( 1 + %s ) )' % E2
    c3p, c3r, c30 = cx('-u ( 1 + %s )' % E2)
    DT3 = DT('M', 'K', E2)
    dt3r = d('remulcld', [llr, c3r], '%s e. RR' % DT3); dt30 = d('mulge0d', [llr, c3r, ll0, c30], '0 <_ %s' % DT3)
    T3 = '( %s x. %s )' % (ZE, DT3)
    t3r = d('remulcld', [d('rpred', [zep], '%s e. RR' % ZE), dt3r], '%s e. RR' % T3); t30 = d('mulge0d', [d('rpred', [zep], '%s e. RR' % ZE), dt3r, d('rpge0d', [zep], '0 <_ %s' % ZE), dt30], '0 <_ %s' % T3)
    dtr = d('remulcld', [llr, c1r], '%s e. RR' % DTM)
    clf = Closure(w, B0, {T1: ('RR', t1r), T2: ('RR', t2r), T3: ('RR', t3r), DTM: ('RR', dtr)})
    for a in (T1, T2, T3, DTM):
        clf.atom(a)
    RHS = PTR('M')
    # ---- case 1: not prime
    A1 = '( %s /\\ -. M e. Prime )' % B0
    L1 = lambda st: lift(w, st, A1)
    np_ = w.s([], 'simpr', '( %s -> -. M e. Prime )' % A1)
    bnv = D(w, A1, 'syl', [np_, w.inst('iffalse')], '%s = %s' % (BN('M'), Yb))
    Q4 = '( 1 / 4 )'
    lp = D(w, A1, 'syl3anc', [w.s([num.rp(w, Q4)], 'a1i', '( %s -> %s e. RR+ )' % (A1, Q4)), L1(kn), L1(mn), w.inst('kdlogpow')],
           '%s <_ ( ( ( ! ` K ) x. ( M ^c %s ) ) / ( %s ^ K ) )' % (LK, Q4, Q4))
    X4 = '( ( ! ` K ) x. ( M ^c %s ) )' % Q4
    m14p, m14r, m140 = [lift(w, x, A1) for x in cx(Q4)]
    x4c = D(w, A1, 'mulcld', [D(w, A1, 'nncnd', [D(w, A1, 'faccld', [L1(kn)], '( ! ` K ) e. NN')], '( ! ` K ) e. CC'), D(w, A1, 'rpcnd', [m14p], '( M ^c %s ) e. CC' % Q4)], '%s e. CC' % X4)
    p4 = D(w, A1, 'exprecd', [a1(w, A1, '4cn', '4 e. CC'), a1(w, A1, '4ne0', '4 =/= 0'), D(w, A1, 'nn0zd', [L1(kn)], 'K e. ZZ')], '( %s ^ K ) = ( 1 / ( 4 ^ K ) )' % Q4)
    P4K = '( 4 ^ K )'
    p4c = D(w, A1, 'expcld', [a1(w, A1, '4cn', '4 e. CC'), L1(kn)], '%s e. CC' % P4K)
    p4n = D(w, A1, 'expne0d', [a1(w, A1, '4cn', '4 e. CC'), a1(w, A1, '4ne0', '4 =/= 0'), D(w, A1, 'nn0zd', [L1(kn)], 'K e. ZZ')], '%s =/= 0' % P4K)
    dd1 = D(w, A1, 'oveq2d', [p4], '( %s / ( %s ^ K ) ) = ( %s / ( 1 / %s ) )' % (X4, Q4, X4, P4K))
    dd2 = D(w, A1, 'divdiv2d', [x4c, a1(w, A1, 'ax-1cn', '1 e. CC'), p4c, a1(w, A1, 'ax-1ne0', '1 =/= 0'), p4n], '( %s / ( 1 / %s ) ) = ( ( %s x. %s ) / 1 )' % (X4, P4K, X4, P4K))
    dd3 = D(w, A1, 'div1d', [D(w, A1, 'mulcld', [x4c, p4c], '( %s x. %s ) e. CC' % (X4, P4K))], '( ( %s x. %s ) / 1 ) = ( %s x. %s )' % (X4, P4K, X4, P4K))
    BND = '( %s x. %s )' % (X4, P4K)
    lp2 = D(w, A1, 'breqtrd', [lp, chain(w, A1, ['( %s / ( %s ^ K ) )' % (X4, Q4), '( %s / ( 1 / %s ) )' % (X4, P4K), '( ( %s x. %s ) / 1 )' % (X4, P4K), BND], [dd1, dd2, dd3])],
            '%s <_ %s' % (LK, BND))
    bndr = D(w, A1, 'remulcld', [D(w, A1, 'remulcld', [D(w, A1, 'nnred', [D(w, A1, 'faccld', [L1(kn)], '( ! ` K ) e. NN')], '( ! ` K ) e. RR'), m14r], '%s e. RR' % X4),
                                 D(w, A1, 'reexpcld', [a1(w, A1, '4re', '4 e. RR'), L1(kn)], '%s e. RR' % P4K)], '%s e. RR' % BND)
    s1 = D(w, A1, 'lemul2ad', [L1(lk), bndr, L1(lm), L1(lm0), lp2], '%s <_ ( ( Lam ` M ) x. %s )' % (LL, BND))
    LB = '( ( Lam ` M ) x. %s )' % BND
    lbr = D(w, A1, 'remulcld', [L1(lm), bndr], '%s e. RR' % LB)
    s2 = D(w, A1, 'lemul1ad', [L1(llr), lbr, L1(c1r), L1(c10), s1], '%s <_ ( %s x. %s )' % (DTM, LB, C1))
    C2 = '( M ^c -u 1 )'
    c2p, c2r, c20 = [lift(w, x, A1) for x in cx('-u 1')]
    ce = D(w, A1, 'cxplead', [L1(mr), L1(m1), L1(cl.mem('-u ( 1 + E )', 'RR')), L1(cl.mem('-u 1', 'RR')),
                              linarith(w, A1, [L1(d('rpge0d', [ep], '0 <_ E'))], '-u ( 1 + E ) <_ -u 1', closure=Closure(w, A1, {'E': ('RR', L1(er))}))], '%s <_ %s' % (C1, C2))
    lb0 = D(w, A1, 'mulge0d', [L1(lm), bndr, L1(lm0), D(w, A1, 'mulge0d', [D(w, A1, 'remulcld', [D(w, A1, 'nnred', [D(w, A1, 'faccld', [L1(kn)], '( ! ` K ) e. NN')], '( ! ` K ) e. RR'), m14r], '%s e. RR' % X4),
                                                                              D(w, A1, 'reexpcld', [a1(w, A1, '4re', '4 e. RR'), L1(kn)], '%s e. RR' % P4K),
                                                                              D(w, A1, 'mulge0d', [D(w, A1, 'nnred', [D(w, A1, 'faccld', [L1(kn)], '( ! ` K ) e. NN')], '( ! ` K ) e. RR'), m14r,
                                                                                                   D(w, A1, 'nn0ge0d', [D(w, A1, 'faccld' if False else 'nnnn0d', [D(w, A1, 'faccld', [L1(kn)], '( ! ` K ) e. NN')], '( ! ` K ) e. NN0')], '0 <_ ( ! ` K )'), m140], '0 <_ %s' % X4),
                                                                              D(w, A1, 'expge0d', [a1(w, A1, '4re', '4 e. RR'), L1(kn), w.s([num.le_nat(w, 0, 4)], 'a1i', '( %s -> 0 <_ 4 )' % A1)], '0 <_ %s' % P4K)], '0 <_ %s' % BND)],
             '0 <_ %s' % LB)
    s3 = D(w, A1, 'lemul2ad', [L1(c1r), c2r, lbr, lb0, ce], '( %s x. %s ) <_ ( %s x. %s )' % (LB, C1, LB, C2))
    cl1 = Closure(w, A1, {'( Lam ` M )': ('CC', D(w, A1, 'recnd', [L1(lm)], '( Lam ` M ) e. CC')), '( ! ` K )': ('CC', D(w, A1, 'nncnd', [D(w, A1, 'faccld', [L1(kn)], '( ! ` K ) e. NN')], '( ! ` K ) e. CC')),
                          '( M ^c %s )' % Q4: ('CC', D(w, A1, 'rpcnd', [m14p], '( M ^c %s ) e. CC' % Q4)), P4K: ('CC', p4c), C2: ('CC', D(w, A1, 'rpcnd', [c2p], '%s e. CC' % C2))})
    for a in ('( Lam ` M )', '( ! ` K )', '( M ^c %s )' % Q4, P4K, C2):
        cl1.atom(a)
    e1 = ringeq(w, A1, '( %s x. %s )' % (LB, C2), '( %s x. ( ( Lam ` M ) x. ( ( M ^c %s ) x. %s ) ) )' % (F4, Q4, C2), cl1)
    ea = D(w, A1, 'cxpaddd', [L1(mc), D(w, A1, 'nnne0d', [L1(mn)], 'M =/= 0'), w.s([num.cc(w, Q4)], 'a1i', '( %s -> %s e. CC )' % (A1, Q4)), D(w, A1, 'negcld', [a1(w, A1, 'ax-1cn', '1 e. CC')], '-u 1 e. CC')],
           '( M ^c ( %s + -u 1 ) ) = ( ( M ^c %s ) x. %s )' % (Q4, Q4, C2))
    eb = D(w, A1, 'oveq2d', [ringeq(w, A1, '( %s + -u 1 )' % Q4, '-u ( 3 / 4 )', Closure(w, A1, {}))], '( M ^c ( %s + -u 1 ) ) = %s' % (Q4, M34))
    ec = D(w, A1, 'eqtr3d', [ea, eb], '( ( M ^c %s ) x. %s ) = %s' % (Q4, C2, M34))
    e2 = D(w, A1, 'oveq2d', [D(w, A1, 'oveq2d', [ec], '( ( Lam ` M ) x. ( ( M ^c %s ) x. %s ) ) = %s' % (Q4, C2, Yb))], '( %s x. ( ( Lam ` M ) x. ( ( M ^c %s ) x. %s ) ) ) = ( %s x. %s )' % (F4, Q4, C2, F4, Yb))
    e3 = D(w, A1, 'oveq2d', [bnv], '%s = ( %s x. %s )' % (T1, F4, Yb))
    ee = D(w, A1, 'eqtr4d', [D(w, A1, 'eqtrd', [e1, e2], '( %s x. %s ) = ( %s x. %s )' % (LB, C2, F4, Yb)), e3], '( %s x. %s ) = %s' % (LB, C2, T1))
    k1 = D(w, A1, 'letrd', [L1(dtr), D(w, A1, 'remulcld', [lbr, L1(c1r)], '( %s x. %s ) e. RR' % (LB, C1)), D(w, A1, 'remulcld', [lbr, c2r], '( %s x. %s ) e. RR' % (LB, C2)), s2, s3],
           '%s <_ ( %s x. %s )' % (DTM, LB, C2))
    k2 = D(w, A1, 'breqtrd', [k1, ee], '%s <_ %s' % (DTM, T1))
    clf1 = Closure(w, A1, {T1: ('RR', L1(t1r)), T2: ('RR', L1(t2r)), T3: ('RR', L1(t3r)), DTM: ('RR', L1(dtr))})
    for a in (T1, T2, T3, DTM):
        clf1.atom(a)
    case1 = linarith(w, A1, [k2, L1(t20), L1(t30)], '%s <_ %s' % (DTM, RHS), closure=clf1)
    # ---- case 2: M <_ Y
    A2 = '( %s /\\ -. Y < M )' % B0
    L2 = lambda st: lift(w, st, A2)
    my = D(w, A2, 'mpbird', [w.s([], 'simpr', '( %s -> -. Y < M )' % A2), D(w, A2, 'syl2anc', [L2(mr), L2(yr), w.inst('lenlt')], '( M <_ Y <-> -. Y < M )')], 'M <_ Y')
    lly = D(w, A2, 'mpbid', [my, D(w, A2, 'logled', [L2(mrp), L2(ypp)], '( M <_ Y <-> ( log ` M ) <_ ( log ` Y ) )')], '( log ` M ) <_ ( log ` Y )')
    lky = D(w, A2, 'leexp1ad', [L2(lg), D(w, A2, 'relogcld', [L2(ypp)], '( log ` Y ) e. RR'), L2(kn), L2(lg0), lly], '%s <_ %s' % (LK, LY))
    q1 = D(w, A2, 'lemul2ad', [L2(lk), L2(lyr), L2(lm), L2(lm0), lky], '%s <_ ( ( Lam ` M ) x. %s )' % (LL, LY))
    q2 = D(w, A2, 'lemul1ad', [L2(llr), D(w, A2, 'remulcld', [L2(lm), L2(lyr)], '( ( Lam ` M ) x. %s ) e. RR' % LY), L2(c1r), L2(c10), q1], '%s <_ ( ( ( Lam ` M ) x. %s ) x. %s )' % (DTM, LY, C1))
    cl2 = Closure(w, A2, {'( Lam ` M )': ('CC', D(w, A2, 'recnd', [L2(lm)], '( Lam ` M ) e. CC')), LY: ('CC', D(w, A2, 'recnd', [L2(lyr)], '%s e. CC' % LY)), C1: ('CC', D(w, A2, 'rpcnd', [L2(c1p)], '%s e. CC' % C1))})
    for a in ('( Lam ` M )', LY, C1):
        cl2.atom(a)
    q3 = D(w, A2, 'breqtrd', [q2, ringeq(w, A2, '( ( ( Lam ` M ) x. %s ) x. %s )' % (LY, C1), T2, cl2)], '%s <_ %s' % (DTM, T2))
    clf2 = Closure(w, A2, {T1: ('RR', L2(t1r)), T2: ('RR', L2(t2r)), T3: ('RR', L2(t3r)), DTM: ('RR', L2(dtr))})
    for a in (T1, T2, T3, DTM):
        clf2.atom(a)
    case2 = linarith(w, A2, [q3, L2(t10), L2(t30)], '%s <_ %s' % (DTM, RHS), closure=clf2)
    # ---- case 3: Z < M
    A3 = '( %s /\\ -. M <_ Z )' % B0
    L3 = lambda st: lift(w, st, A3)
    zr = d('rpred', [zp], 'Z e. RR')
    zm = D(w, A3, 'mpbird', [w.s([], 'simpr', '( %s -> -. M <_ Z )' % A3), D(w, A3, 'ltnled', [L3(zr), L3(mr)], '( Z < M <-> -. M <_ Z )')], 'Z < M')
    zml = D(w, A3, 'ltled', [L3(zr), L3(mr), zm], 'Z <_ M')
    e2p = L3(cl.mem(E2, 'RR+'))
    e2r = D(w, A3, 'rpred', [e2p], '%s e. RR' % E2)
    ME_ = '( M ^c -u %s )' % E2
    zc = D(w, A3, 'cxple2ad', [L3(zr), L3(d('rpge0d', [zp], '0 <_ Z')), L3(mr), e2r, D(w, A3, 'rpge0d', [e2p], '0 <_ %s' % E2), zml], '( Z ^c %s ) <_ ( M ^c %s )' % (E2, E2))
    zcp = D(w, A3, 'rpcxpcld', [L3(zp), e2r], '( Z ^c %s ) e. RR+' % E2); mcp = D(w, A3, 'rpcxpcld', [L3(mrp), e2r], '( M ^c %s ) e. RR+' % E2)
    rl = D(w, A3, 'lediv2ad', [zcp, mcp, a1(w, A3, '1re', '1 e. RR'), a1(w, A3, '0le1', '0 <_ 1'), zc], '( 1 / ( M ^c %s ) ) <_ ( 1 / ( Z ^c %s ) )' % (E2, E2))
    n1 = D(w, A3, 'cxpnegd', [L3(mc), D(w, A3, 'nnne0d', [L3(mn)], 'M =/= 0'), D(w, A3, 'rpcnd', [e2p], '%s e. CC' % E2)], '%s = ( 1 / ( M ^c %s ) )' % (ME_, E2))
    n2 = D(w, A3, 'cxpnegd', [D(w, A3, 'rpcnd', [L3(zp)], 'Z e. CC'), D(w, A3, 'rpne0d', [L3(zp)], 'Z =/= 0'), D(w, A3, 'rpcnd', [e2p], '%s e. CC' % E2)], '%s = ( 1 / ( Z ^c %s ) )' % (ZE, E2))
    mz = D(w, A3, 'breqtrrd', [D(w, A3, 'eqbrtrd', [n1, rl], '%s <_ ( 1 / ( Z ^c %s ) )' % (ME_, E2)), n2], '%s <_ %s' % (ME_, ZE))
    cla = Closure(w, A3, {'E': ('RR', L3(er))})
    ex3 = ringeq(w, A3, '-u ( 1 + E )', '( -u ( 1 + %s ) + -u %s )' % (E2, E2), cla)
    ca = D(w, A3, 'cxpaddd', [L3(mc), D(w, A3, 'nnne0d', [L3(mn)], 'M =/= 0'), D(w, A3, 'recnd', [L3(cl.mem('-u ( 1 + %s )' % E2, 'RR'))], '-u ( 1 + %s ) e. CC' % E2),
                              D(w, A3, 'recnd', [L3(cl.mem('-u %s' % E2, 'RR'))], '-u %s e. CC' % E2)], '( M ^c ( -u ( 1 + %s ) + -u %s ) ) = ( %s x. %s )' % (E2, E2, C3, ME_))
    c1e = D(w, A3, 'eqtrd', [D(w, A3, 'oveq2d', [ex3], '%s = ( M ^c ( -u ( 1 + %s ) + -u %s ) )' % (C1, E2, E2)), ca], '%s = ( %s x. %s )' % (C1, C3, ME_))
    mer = D(w, A3, 'rpred', [D(w, A3, 'rpcxpcld', [L3(mrp), L3(cl.mem('-u %s' % E2, 'RR'))], '%s e. RR+' % ME_)], '%s e. RR' % ME_)
    w1 = D(w, A3, 'lemul2ad', [mer, D(w, A3, 'rpred', [L3(zep)], '%s e. RR' % ZE), L3(c3r), L3(c30), mz], '( %s x. %s ) <_ ( %s x. %s )' % (C3, ME_, C3, ZE))
    w2 = D(w, A3, 'lemul2ad', [D(w, A3, 'remulcld', [L3(c3r), mer], '( %s x. %s ) e. RR' % (C3, ME_)), D(w, A3, 'remulcld', [L3(c3r), D(w, A3, 'rpred', [L3(zep)], '%s e. RR' % ZE)], '( %s x. %s ) e. RR' % (C3, ZE)),
                               L3(llr), L3(ll0), w1], '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (LL, C3, ME_, LL, C3, ZE))
    dte = D(w, A3, 'oveq2d', [c1e], '%s = ( %s x. ( %s x. %s ) )' % (DTM, LL, C3, ME_))
    cl3 = Closure(w, A3, {'( Lam ` M )': ('CC', D(w, A3, 'recnd', [L3(lm)], '( Lam ` M ) e. CC')), LK: ('CC', D(w, A3, 'recnd', [L3(lk)], '%s e. CC' % LK)), C3: ('CC', D(w, A3, 'rpcnd', [L3(c3p)], '%s e. CC' % C3)),
                          ZE: ('CC', D(w, A3, 'rpcnd', [L3(zep)], '%s e. CC' % ZE))})
    for a in ('( Lam ` M )', LK, C3, ZE):
        cl3.atom(a)
    w3 = ringeq(w, A3, '( %s x. ( %s x. %s ) )' % (LL, C3, ZE), T3, cl3)
    w4 = D(w, A3, 'breqtrd', [D(w, A3, 'eqbrtrd', [dte, w2], '%s <_ ( %s x. ( %s x. %s ) )' % (DTM, LL, C3, ZE)), w3], '%s <_ %s' % (DTM, T3))
    clf3 = Closure(w, A3, {T1: ('RR', L3(t1r)), T2: ('RR', L3(t2r)), T3: ('RR', L3(t3r)), DTM: ('RR', L3(dtr))})
    for a in (T1, T2, T3, DTM):
        clf3.atom(a)
    case3 = linarith(w, A3, [w4, L3(t10), L3(t20)], '%s <_ %s' % (DTM, RHS), closure=clf3)
    j = w.s([case1, case2, case3], '3jaodan', '( ( %s /\\ ( -. M e. Prime \\/ -. Y < M \\/ -. M <_ Z ) ) -> %s <_ %s )' % (B0, DTM, RHS))
    # rearrange ( B0 /\ dis ) to A0
    g1_ = w.s([], 'simp1', '( %s -> ( E e. RR+ /\\ K e. NN0 ) )' % A0)
    g2_ = w.s([], 'simp2', '( %s -> ( ( Y e. RR /\\ 1 <_ Y ) /\\ Z e. RR+ ) )' % A0)
    g3_ = w.s([], 'simp3', '( %s -> ( M e. NN /\\ ( -. M e. Prime \\/ -. Y < M \\/ -. M <_ Z ) ) )' % A0)
    b0 = D(w, A0, '3jca', [g1_, g2_, D(w, A0, 'simpld', [g3_], 'M e. NN')], B0)
    fin = D(w, A0, 'syl2anc', [b0, D(w, A0, 'simprd', [g3_], '( -. M e. Prime \\/ -. Y < M \\/ -. M <_ Z )'), j], '%s <_ %s' % (DTM, RHS))
    w.qed([fin], 'idi', S['kd2pt'])
    return only_run(w, only)


def dtcong(w, x, y, K, U):
    H = '%s = %s' % (x, y)
    a = w.s([w.s([], 'fveq2', '( %s -> ( Lam ` %s ) = ( Lam ` %s ) )' % (H, x, y)), w.s([w.s([], 'fveq2', '( %s -> ( log ` %s ) = ( log ` %s ) )' % (H, x, y))], 'oveq1d',
                                                                                      '( %s -> ( ( log ` %s ) ^ %s ) = ( ( log ` %s ) ^ %s ) )' % (H, x, K, y, K))],
            'oveq12d', '( %s -> ( ( Lam ` %s ) x. ( ( log ` %s ) ^ %s ) ) = ( ( Lam ` %s ) x. ( ( log ` %s ) ^ %s ) ) )' % (H, x, x, K, y, y, K))
    b = w.s([], 'oveq1', '( %s -> ( %s ^c -u ( 1 + %s ) ) = ( %s ^c -u ( 1 + %s ) ) )' % (H, x, U, y, U))
    return w.s([a, b], 'oveq12d', '( %s -> %s = %s )' % (H, DT(x, K, U), DT(y, K, U)))


def dtfacts(w, Ah, k, kn, K, kk, U, ur):
    d = lambda ref, h, c: D(w, Ah, ref, h, c)
    lm = d('syl', [kn, w.inst('vmacl')], '( Lam ` %s ) e. RR' % k); lm0 = d('syl', [kn, w.inst('vmage0')], '0 <_ ( Lam ` %s )' % k)
    lg = d('relogcld', [d('nnrpd', [kn], '%s e. RR+' % k)], '( log ` %s ) e. RR' % k)
    lg0 = d('logge0d', [d('nnred', [kn], '%s e. RR' % k), d('nnge1d', [kn], '1 <_ %s' % k)], '0 <_ ( log ` %s )' % k)
    lk = d('reexpcld', [lg, kk], '( ( log ` %s ) ^ %s ) e. RR' % (k, K)); lk0 = d('expge0d', [lg, kk, lg0], '0 <_ ( ( log ` %s ) ^ %s )' % (k, K))
    ex = d('renegcld', [d('readdcld', [a1(w, Ah, '1re', '1 e. RR'), ur], '( 1 + %s ) e. RR' % U)], '-u ( 1 + %s ) e. RR' % U)
    cx = d('rpcxpcld', [d('nnrpd', [kn], '%s e. RR+' % k), ex], '( %s ^c -u ( 1 + %s ) ) e. RR+' % (k, U))
    LL = '( ( Lam ` %s ) x. ( ( log ` %s ) ^ %s ) )' % (k, k, K)
    llr = d('remulcld', [lm, lk], '%s e. RR' % LL); ll0 = d('mulge0d', [lm, lk, lm0, lk0], '0 <_ %s' % LL)
    r = d('remulcld', [llr, d('rpred', [cx], '( %s ^c -u ( 1 + %s ) ) e. RR' % (k, U))], '%s e. RR' % DT(k, K, U))
    z = d('mulge0d', [llr, d('rpred', [cx], '( %s ^c -u ( 1 + %s ) ) e. RR' % (k, U)), ll0, d('rpge0d', [cx], '0 <_ ( %s ^c -u ( 1 + %s ) )' % (k, U))], '0 <_ %s' % DT(k, K, U))
    return r, z


def gen_dgp():
    w = W('kd2dgp', 'A finite sum of the diagonal terms ` Lam ( k ) ( log k )^K k^-(1+U) ` over ` A C_ NN ` is at most ~ kddiag2 ` K! e ( 5 / 4 ) ( K + 2 ) / U^(K+1) ` ( ~ isumless ).')
    A0 = S['kd2dgp'].split(' -> sum_')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simpl', [], '( ( U e. RR+ /\\ U <_ %s ) /\\ K e. NN0 )' % R120); g2 = d('simpr', [], '( A e. Fin /\\ A C_ NN )')
    up = d('simpld', [d('simpld', [g1], '( U e. RR+ /\\ U <_ %s )' % R120)], 'U e. RR+'); ur = d('rpred', [up], 'U e. RR'); kn = d('simprd', [g1], 'K e. NN0')
    af = d('simpld', [g2], 'A e. Fin'); ass = d('simprd', [g2], 'A C_ NN')
    dg = d('syl', [g1, w.inst('kddiag2')], split_imp(stmt('kddiag2'))[1])
    Fn = '( n e. NN |-> %s )' % DT('n', 'K', 'U')
    cv = d('simpld', [dg], 'seq 1 ( + , %s ) e. dom ~~>' % Fn)
    bd = d('simprd', [dg], 'sum_ n e. NN %s <_ %s' % (DT('n', 'K', 'U'), DG2('K', 'U')))
    Ak = '( %s /\\ k e. NN )' % A0
    kk = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    vr, v0 = dtfacts(w, Ak, 'k', kk, 'K', lift(w, kn, Ak), 'U', lift(w, ur, Ak))
    mc = w.s([dtcong(w, 'n', 'k', 'K', 'U')], 'adantl', '( ( %s /\\ n = k ) -> %s = %s )' % (Ak, DT('n', 'K', 'U'), DT('k', 'K', 'U')))
    fv = D(w, Ak, 'fvmptd', [a1(w, Ak, 'eqid', '%s = %s' % (Fn, Fn)), mc, kk, D(w, Ak, 'recnd', [vr], '%s e. CC' % DT('k', 'K', 'U'))], '( %s ` k ) = %s' % (Fn, DT('k', 'K', 'U')))
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    il = d('isumless', [nnu, a1(w, A0, '1z', '1 e. ZZ'), af, ass, fv, vr, v0, cv], 'sum_ k e. A %s <_ sum_ k e. NN %s' % (DT('k', 'K', 'U'), DT('k', 'K', 'U')))
    cb = w.s([dtcong(w, 'k', 'n', 'K', 'U')], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (DT('k', 'K', 'U'), DT('n', 'K', 'U')))
    il2 = d('breqtrd', [il, w.s([cb], 'a1i', '( %s -> sum_ k e. NN %s = sum_ n e. NN %s )' % (A0, DT('k', 'K', 'U'), DT('n', 'K', 'U')))], 'sum_ k e. A %s <_ sum_ n e. NN %s' % (DT('k', 'K', 'U'), DT('n', 'K', 'U')))
    isr = d('eqeltrrd', [w.s([cb], 'a1i', '( %s -> sum_ k e. NN %s = sum_ n e. NN %s )' % (A0, DT('k', 'K', 'U'), DT('n', 'K', 'U'))),
                         d('isumrecl', [nnu, a1(w, A0, '1z', '1 e. ZZ'), fv, vr, cv], 'sum_ k e. NN %s e. RR' % DT('k', 'K', 'U'))], 'sum_ n e. NN %s e. RR' % DT('n', 'K', 'U'))
    Aa = '( %s /\\ k e. A )' % A0
    kna = D(w, Aa, 'sseldd', [lift(w, ass, Aa), w.s([], 'simpr', '( %s -> k e. A )' % Aa)], 'k e. NN')
    vra, _ = dtfacts(w, Aa, 'k', kna, 'K', lift(w, kn, Aa), 'U', lift(w, ur, Aa))
    fr = d('fsumrecl', [af, vra], 'sum_ k e. A %s e. RR' % DT('k', 'K', 'U'))
    cl = Closure(w, A0, {'U': ('RR+', up), 'K': ('NN0', kn)})
    cl.leaf('( ! ` K )', 'RR+', d('nnrpd', [d('faccld', [kn], '( ! ` K ) e. NN')], '( ! ` K ) e. RR+'))
    e1 = d('rpred', [a1(w, A0, None, None)] if False else [d('rpefcld' if False else 'syl', [a1(w, A0, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR')
    cl.leaf('( exp ` 1 )', 'RR', e1)
    fin = d('letrd', [fr, isr, cl.mem(DG2('K', 'U'), 'RR'), il2, bd], 'sum_ k e. A %s <_ %s' % (DT('k', 'K', 'U'), DG2('K', 'U')))
    w.qed([fin], 'idi', S['kd2dgp'])
    return only_run(w, only)


def gen_psum():
    w = W('kd2psum', 'Partial sums of Lean ` KDerivDetect.norm_LSeries_sub_window_le ` : for ` W >_ |_ X2 ` , ` abs ( sum_ n <_ W a_n - Dwin ) ` is at most the three tails (prime powers ~ kd2npf , ` n <_ X1 ` ~ kd2vmp , ` n > X2 ` ~ kd2dgp ) through the pointwise majorant ~ kd2pt and ~ kdterm .')
    from kd2_c import ltcc
    A0 = S['kd2psum'].split(' -> ( abs `')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    sh = d('simpl', [], SUBH); gw = d('simpr', [], '( W e. NN /\\ ( |_ ` Z ) <_ W )')
    nxh = d('simp1d', [sh], NXH); h2 = d('simp2d', [sh], '( T e. RR /\\ E e. RR+ /\\ E <_ %s )' % R120); h3 = d('simp3d', [sh], '( ( Y e. RR /\\ 1 <_ Y ) /\\ ( Z e. RR /\\ Y <_ Z ) /\\ J e. NN0 )')
    tr = d('simp1d', [h2], 'T e. RR'); ep = d('simp2d', [h2], 'E e. RR+'); e20 = d('simp3d', [h2], 'E <_ %s' % R120)
    gy = d('simp1d', [h3], '( Y e. RR /\\ 1 <_ Y )'); gz = d('simp2d', [h3], '( Z e. RR /\\ Y <_ Z )'); jn = d('simp3d', [h3], 'J e. NN0')
    yr = d('simpld', [gy], 'Y e. RR'); y1 = d('simprd', [gy], '1 <_ Y'); zr = d('simpld', [gz], 'Z e. RR'); yz = d('simprd', [gz], 'Y <_ Z')
    wn = d('simpld', [gw], 'W e. NN'); fw = d('simprd', [gw], '( |_ ` Z ) <_ W')
    er = d('rpred', [ep], 'E e. RR')
    K = '( J + 1 )'; kn = d('syl', [jn, w.inst('peano2nn0')], '%s e. NN0' % K)
    cly = Closure(w, A0, {'Y': ('RR', yr), 'Z': ('RR', zr)})
    zp = d('elrpd', [zr, linarith(w, A0, [y1, yz], '0 < Z', closure=cly)], 'Z e. RR+')
    S0T = S0()
    FW = '( 1 ... W )'; PS = PSET('Y', 'Z'); DF = '( %s \\ %s )' % (FW, PS)
    wz = d('nnzd', [wn], 'W e. ZZ'); flz = d('flcld', [zr], '( |_ ` Z ) e. ZZ')
    wu = d('sylibr', [d('3jca', [flz, wz, fw], '( ( |_ ` Z ) e. ZZ /\\ W e. ZZ /\\ ( |_ ` Z ) <_ W )'),
                      w.s([], 'eluz2', '( W e. ( ZZ>= ` ( |_ ` Z ) ) <-> ( ( |_ ` Z ) e. ZZ /\\ W e. ZZ /\\ ( |_ ` Z ) <_ W ) )')], 'W e. ( ZZ>= ` ( |_ ` Z ) )')
    pss = d('sstrd', [a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PS), d('syl', [wu, w.inst('fzss2')], '( 1 ... ( |_ ` Z ) ) C_ %s' % FW)], '%s C_ %s' % (PS, FW))
    ffw = d('fzfid', [], '%s e. Fin' % FW)
    a_ = lambda n: LT(K, S0T, n)
    s0c = d('addcld', [d('recnd', [d('readdcld', [a1(w, A0, '1re', '1 e. RR'), er], '( 1 + E ) e. RR')], '( 1 + E ) e. CC'),
                       d('mulcld', [a1(w, A0, 'ax-icn', '_i e. CC'), d('recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % S0T)
    An = '( %s /\\ n e. %s )' % (A0, FW)
    nnn = D(w, An, 'syl', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FW)), w.inst('elfznn')], 'n e. NN')
    anc = ltcc(w, An, 'n', nnn, lift(w, nxh, An), (lift(w, kn, An), K), (lift(w, s0c, An), S0T))
    un = d('mpbi' if False else 'sylib', [pss, w.s([], 'undif', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (PS, FW, PS, DF, FW))], '( %s u. %s ) = %s' % (PS, DF, FW))
    spl = d('fsumsplit', [a1(w, A0, 'disjdif', '( %s i^i %s ) = (/)' % (PS, DF)), d('eqcomd', [un], '%s = ( %s u. %s )' % (FW, PS, DF)), ffw, anc],
            'sum_ n e. %s %s = ( sum_ n e. %s %s + sum_ n e. %s %s )' % (FW, a_('n'), PS, a_('n'), DF, a_('n')))
    # DW = sum over PS of a
    Ap = '( %s /\\ p e. %s )' % (A0, PS)
    pps = w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PS))
    ae = w.s([w.s([], 'eleq1', '( a = p -> ( a e. Prime <-> p e. Prime ) )'), w.s([], 'breq2', '( a = p -> ( Y < a <-> Y < p ) )')], 'anbi12d',
             '( a = p -> ( ( a e. Prime /\\ Y < a ) <-> ( p e. Prime /\\ Y < p ) ) )')
    elp = w.s([ae], 'elrab', '( p e. %s <-> ( p e. ( 1 ... ( |_ ` Z ) ) /\\ ( p e. Prime /\\ Y < p ) ) )' % PS)
    ppr = D(w, Ap, 'simprld' if False else 'simpld', [D(w, Ap, 'simprd', [D(w, Ap, 'mpbid', [pps, w.s([elp], 'a1i', '( %s -> ( p e. %s <-> ( p e. ( 1 ... ( |_ ` Z ) ) /\\ ( p e. Prime /\\ Y < p ) ) ) )' % (Ap, PS))],
                                                                  '( p e. ( 1 ... ( |_ ` Z ) ) /\\ ( p e. Prime /\\ Y < p ) )')], '( p e. Prime /\\ Y < p )')], 'p e. Prime')
    pw = use(w, Ap, 'kd2pwt', {'P': 'p'}, D(w, Ap, '3jca', [lift(w, nxh, Ap), D(w, Ap, '3jca', [lift(w, tr, Ap), lift(w, er, Ap), lift(w, jn, Ap)], '( T e. RR /\\ E e. RR /\\ J e. NN0 )'), ppr],
                                             '( %s /\\ ( T e. RR /\\ E e. RR /\\ J e. NN0 ) /\\ p e. Prime )' % NXH))
    dw1 = d('sumeq2dv', [pw], 'sum_ p e. %s %s = %s' % (PS, a_('p'), DWIN('J', 'Y', 'Z')))
    cb = w.s([tcong(w, 'p', 'n', K, S0T)], 'cbvsumv', 'sum_ p e. %s %s = sum_ n e. %s %s' % (PS, a_('p'), PS, a_('n')))
    dw = d('eqtr3d', [dw1, w.s([cb], 'a1i', '( %s -> sum_ p e. %s %s = sum_ n e. %s %s )' % (A0, PS, a_('p'), PS, a_('n')))], '%s = sum_ n e. %s %s' % (DWIN('J', 'Y', 'Z'), PS, a_('n')))
    SPS = 'sum_ n e. %s %s' % (PS, a_('n')); SDF = 'sum_ n e. %s %s' % (DF, a_('n')); SFW = 'sum_ n e. %s %s' % (FW, a_('n'))
    Aps = '( %s /\\ n e. %s )' % (A0, PS)
    ancps = D(w, Aps, 'mpd', [D(w, Aps, 'sseldd', [lift(w, pss, Aps), w.s([], 'simpr', '( %s -> n e. %s )' % (Aps, PS))], 'n e. %s' % FW), lift(w, w.s([anc], 'ex', '( %s -> ( n e. %s -> %s e. CC ) )' % (A0, FW, a_('n'))), Aps)],
              '%s e. CC' % a_('n'))
    Adf = '( %s /\\ n e. %s )' % (A0, DF)
    ndf = w.s([], 'simpr', '( %s -> n e. %s )' % (Adf, DF))
    nfw = D(w, Adf, 'syl', [ndf, w.inst('eldifi')], 'n e. %s' % FW)
    ancdf = D(w, Adf, 'mpd', [nfw, lift(w, w.s([anc], 'ex', '( %s -> ( n e. %s -> %s e. CC ) )' % (A0, FW, a_('n'))), Adf)], '%s e. CC' % a_('n'))
    ffps = d('ssfid', [ffw, pss], '%s e. Fin' % PS); ffdf = d('ssfid', [ffw, d('difssd', [], '%s C_ %s' % (DF, FW))], '%s e. Fin' % DF)
    sps = d('fsumcl', [ffps, ancps], '%s e. CC' % SPS); sdf = d('fsumcl', [ffdf, ancdf], '%s e. CC' % SDF)
    df1 = d('eqtrd', [d('oveq12d', [spl, dw], '( %s - %s ) = ( ( %s + %s ) - %s )' % (SFW, DWIN('J', 'Y', 'Z'), SPS, SDF, SPS)), d('pncan2d', [sps, sdf], '( ( %s + %s ) - %s ) = %s' % (SPS, SDF, SPS, SDF))],
             '( %s - %s ) = %s' % (SFW, DWIN('J', 'Y', 'Z'), SDF))
    # b1..b4
    b1 = d('fsumabs', [ffdf, ancdf], '( abs ` %s ) <_ sum_ n e. %s ( abs ` %s )' % (SDF, DF, a_('n')))
    nndf = D(w, Adf, 'syl', [nfw, w.inst('elfznn')], 'n e. NN')
    kt = use(w, Adf, 'kdterm', {'S': S0T, 'K': K, 'M': 'n'}, D(w, Adf, 'jca', [lift(w, nxh, Adf), D(w, Adf, '3jca', [lift(w, s0c, Adf), lift(w, kn, Adf), nndf], '( %s e. CC /\\ %s e. NN0 /\\ n e. NN )' % (S0T, K))],
                                                                  '( %s /\\ ( %s e. CC /\\ %s e. NN0 /\\ n e. NN ) )' % (NXH, S0T, K)))
    rs = D(w, Adf, 'syl2anc', [D(w, Adf, 'readdcld', [a1(w, Adf, '1re', '1 e. RR'), lift(w, er, Adf)], '( 1 + E ) e. RR'), lift(w, tr, Adf), w.inst('crre')], '( Re ` %s ) = ( 1 + E )' % S0T)
    kt2 = D(w, Adf, 'breqtrd', [kt, D(w, Adf, 'oveq2d', [D(w, Adf, 'negeqd', [rs], '-u ( Re ` %s ) = -u ( 1 + E )' % S0T)], '( n ^c -u ( Re ` %s ) ) = ( n ^c -u ( 1 + E ) )' % S0T) if False else
                                  D(w, Adf, 'oveq2d', [D(w, Adf, 'oveq2d', [D(w, Adf, 'negeqd', [rs], '-u ( Re ` %s ) = -u ( 1 + E )' % S0T)], '( n ^c -u ( Re ` %s ) ) = ( n ^c -u ( 1 + E ) )' % S0T)],
                                    '( ( ( Lam ` n ) x. ( ( log ` n ) ^ %s ) ) x. ( n ^c -u ( Re ` %s ) ) ) = %s' % (K, S0T, DT('n', K, 'E')))], '( abs ` %s ) <_ %s' % (a_('n'), DT('n', K, 'E')))
    dtr, dt0 = dtfacts(w, Adf, 'n', nndf, K, lift(w, kn, Adf), 'E', lift(w, er, Adf))
    b2 = d('fsumle', [ffdf, D(w, Adf, 'abscld', [ancdf], '( abs ` %s ) e. RR' % a_('n')), dtr, kt2], 'sum_ n e. %s ( abs ` %s ) <_ sum_ n e. %s %s' % (DF, a_('n'), DF, DT('n', K, 'E')))
    # disjunction
    nps = D(w, Adf, 'syl', [ndf, w.inst('eldifn')], '-. n e. %s' % PS)
    An3 = '( %s /\\ ( n e. Prime /\\ Y < n /\\ n <_ Z ) )' % Adf
    g3 = w.s([], 'simpr', '( %s -> ( n e. Prime /\\ Y < n /\\ n <_ Z ) )' % An3)
    nz3 = D(w, An3, 'nnzd', [lift(w, nndf, An3)], 'n e. ZZ')
    nfl = D(w, An3, 'mpbid', [D(w, An3, 'simp3d', [g3], 'n <_ Z'), D(w, An3, 'syl2anc', [lift(w, zr, An3), nz3, w.inst('flge')], '( n <_ Z <-> n <_ ( |_ ` Z ) )')], 'n <_ ( |_ ` Z )')
    nin = D(w, An3, 'elfzd', [a1(w, An3, '1z', '1 e. ZZ'), lift(w, flz, An3), nz3, D(w, An3, 'nnge1d', [lift(w, nndf, An3)], '1 <_ n'), nfl], 'n e. ( 1 ... ( |_ ` Z ) )')
    ae2 = w.s([w.s([], 'eleq1', '( a = n -> ( a e. Prime <-> n e. Prime ) )'), w.s([], 'breq2', '( a = n -> ( Y < a <-> Y < n ) )')], 'anbi12d',
              '( a = n -> ( ( a e. Prime /\\ Y < a ) <-> ( n e. Prime /\\ Y < n ) ) )')
    eln = w.s([ae2], 'elrab', '( n e. %s <-> ( n e. ( 1 ... ( |_ ` Z ) ) /\\ ( n e. Prime /\\ Y < n ) ) )' % PS)
    inps = D(w, An3, 'mpbird', [D(w, An3, 'jca', [nin, D(w, An3, 'jca', [D(w, An3, 'simp1d', [g3], 'n e. Prime'), D(w, An3, 'simp2d', [g3], 'Y < n')], '( n e. Prime /\\ Y < n )')],
                                      '( n e. ( 1 ... ( |_ ` Z ) ) /\\ ( n e. Prime /\\ Y < n ) )'), w.s([eln], 'a1i', '( %s -> ( n e. %s <-> ( n e. ( 1 ... ( |_ ` Z ) ) /\\ ( n e. Prime /\\ Y < n ) ) ) )' % (An3, PS))],
                'n e. %s' % PS)
    nt = D(w, Adf, 'mtod', [nps, w.s([inps], 'ex', '( %s -> ( ( n e. Prime /\\ Y < n /\\ n <_ Z ) -> n e. %s ) )' % (Adf, PS))], '-. ( n e. Prime /\\ Y < n /\\ n <_ Z )')
    dis = D(w, Adf, 'sylib', [nt, w.s([], '3ianor', '( -. ( n e. Prime /\\ Y < n /\\ n <_ Z ) <-> ( -. n e. Prime \\/ -. Y < n \\/ -. n <_ Z ) )')], '( -. n e. Prime \\/ -. Y < n \\/ -. n <_ Z )')
    ptH = D(w, Adf, '3jca', [D(w, Adf, 'jca', [lift(w, ep, Adf), lift(w, kn, Adf)], '( E e. RR+ /\\ %s e. NN0 )' % K), D(w, Adf, 'jca', [lift(w, gy, Adf), lift(w, zp, Adf)], '( ( Y e. RR /\\ 1 <_ Y ) /\\ Z e. RR+ )'),
                             D(w, Adf, 'jca', [nndf, dis], '( n e. NN /\\ ( -. n e. Prime \\/ -. Y < n \\/ -. n <_ Z ) )')],
             '( ( E e. RR+ /\\ %s e. NN0 ) /\\ ( ( Y e. RR /\\ 1 <_ Y ) /\\ Z e. RR+ ) /\\ ( n e. NN /\\ ( -. n e. Prime \\/ -. Y < n \\/ -. n <_ Z ) ) )' % K)
    pt = use(w, Adf, 'kd2pt', {'K': K, 'M': 'n'}, ptH)
    PT = PTR('n', K)
    # PTR >= 0 and real on FW, its three pieces
    F4 = '( ( 4 ^ %s ) x. ( ! ` %s ) )' % (K, K); LY = '( ( log ` Y ) ^ %s )' % K; ZE = '( Z ^c -u ( E / 2 ) )'
    ypp = d('elrpd', [yr, linarith(w, A0, [y1], '0 < Y', closure=cly)], 'Y e. RR+')
    fnn = d('faccld', [kn], '( ! ` %s ) e. NN' % K)
    f4r = d('remulcld', [d('reexpcld', [a1(w, A0, '4re', '4 e. RR'), kn], '( 4 ^ %s ) e. RR' % K), d('nnred', [fnn], '( ! ` %s ) e. RR' % K)], '%s e. RR' % F4)
    f40 = d('mulge0d', [d('reexpcld', [a1(w, A0, '4re', '4 e. RR'), kn], '( 4 ^ %s ) e. RR' % K), d('nnred', [fnn], '( ! ` %s ) e. RR' % K),
                        d('expge0d', [a1(w, A0, '4re', '4 e. RR'), kn, w.s([num.le_nat(w, 0, 4)], 'a1i', '( %s -> 0 <_ 4 )' % A0)], '0 <_ ( 4 ^ %s )' % K),
                        d('nn0ge0d', [d('nnnn0d', [fnn], '( ! ` %s ) e. NN0' % K)], '0 <_ ( ! ` %s )' % K)], '0 <_ %s' % F4)
    lyr = d('reexpcld', [d('relogcld', [ypp], '( log ` Y ) e. RR'), kn], '%s e. RR' % LY)
    ly0 = d('expge0d', [d('relogcld', [ypp], '( log ` Y ) e. RR'), kn, d('logge0d', [yr, y1], '0 <_ ( log ` Y )')], '0 <_ %s' % LY)
    e2p = d('rphalfcld', [ep], '( E / 2 ) e. RR+')
    zep = d('rpcxpcld', [zp, d('renegcld', [d('rpred', [e2p], '( E / 2 ) e. RR')], '-u ( E / 2 ) e. RR')], '%s e. RR+' % ZE)
    zer = d('rpred', [zep], '%s e. RR' % ZE); ze0 = d('rpge0d', [zep], '0 <_ %s' % ZE)
    def pieces(Ah, nn_):
        dd = lambda ref, h, c: D(w, Ah, ref, h, c)
        L = lambda st: lift(w, st, Ah)
        # BN
        m34 = dd('rpcxpcld', [dd('nnrpd', [nn_], 'n e. RR+'), dd('renegcld', [w.s([num.real(w, '( 3 / 4 )')], 'a1i', '( %s -> ( 3 / 4 ) e. RR )' % Ah)], '-u ( 3 / 4 ) e. RR')], '( n ^c -u ( 3 / 4 ) ) e. RR+')
        lm = dd('syl', [nn_, w.inst('vmacl')], '( Lam ` n ) e. RR'); lm0 = dd('syl', [nn_, w.inst('vmage0')], '0 <_ ( Lam ` n )')
        Yb = '( ( Lam ` n ) x. ( n ^c -u ( 3 / 4 ) ) )'
        ybr = dd('remulcld', [lm, dd('rpred', [m34], '( n ^c -u ( 3 / 4 ) ) e. RR')], '%s e. RR' % Yb)
        yb0 = dd('mulge0d', [lm, dd('rpred', [m34], '( n ^c -u ( 3 / 4 ) ) e. RR'), lm0, dd('rpge0d', [m34], '0 <_ ( n ^c -u ( 3 / 4 ) )')], '0 <_ %s' % Yb)
        bnr = dd('ifcld', [a1(w, Ah, '0re', '0 e. RR'), ybr], '%s e. RR' % BN('n'))
        bn0 = ifge0(w, Ah, 'n e. Prime', Yb, yb0)
        vr, v0 = vmfacts(w, Ah, 'n', nn_, L(er))
        dr, d0 = dtfacts(w, Ah, 'n', nn_, K, L(kn), '( E / 2 )', dd('rpred', [L(e2p)], '( E / 2 ) e. RR'))
        T1 = '( %s x. %s )' % (F4, BN('n')); T2 = '( %s x. %s )' % (LY, VMT('n', 'E')); T3 = '( %s x. %s )' % (ZE, DT('n', K, '( E / 2 )'))
        t1r = dd('remulcld', [L(f4r), bnr], '%s e. RR' % T1); t10 = dd('mulge0d', [L(f4r), bnr, L(f40), bn0], '0 <_ %s' % T1)
        t2r = dd('remulcld', [L(lyr), vr], '%s e. RR' % T2); t20 = dd('mulge0d', [L(lyr), vr, L(ly0), v0], '0 <_ %s' % T2)
        t3r = dd('remulcld', [L(zer), dr], '%s e. RR' % T3); t30 = dd('mulge0d', [L(zer), dr, L(ze0), d0], '0 <_ %s' % T3)
        pr = dd('readdcld', [t1r, dd('readdcld', [t2r, t3r], '( %s + %s ) e. RR' % (T2, T3))], '%s e. RR' % PT)
        p0 = dd('addge0d', [t1r, dd('readdcld', [t2r, t3r], '( %s + %s ) e. RR' % (T2, T3)), t10, dd('addge0d', [t2r, t3r, t20, t30], '0 <_ ( %s + %s )' % (T2, T3))], '0 <_ %s' % PT)
        return dict(bnr=bnr, vr=vr, dr=dr, t1r=t1r, t2r=t2r, t3r=t3r, pr=pr, p0=p0, T1=T1, T2=T2, T3=T3)
    PD = pieces(Adf, nndf)
    b3 = d('fsumle', [ffdf, dtr, PD['pr'], pt], 'sum_ n e. %s %s <_ sum_ n e. %s %s' % (DF, DT('n', K, 'E'), DF, PT))
    PF = pieces(An, nnn)
    b4 = d('fsumless', [ffw, PF['pr'], PF['p0'], d('difssd', [], '%s C_ %s' % (DF, FW))], 'sum_ n e. %s %s <_ sum_ n e. %s %s' % (DF, PT, FW, PT))
    T1, T2, T3 = PF['T1'], PF['T2'], PF['T3']
    c = lambda st, f: D(w, An, 'recnd', [st], '%s e. CC' % f)
    a23 = d('fsumadd', [ffw, c(PF['t2r'], T2), c(PF['t3r'], T3)], 'sum_ n e. %s ( %s + %s ) = ( sum_ n e. %s %s + sum_ n e. %s %s )' % (FW, T2, T3, FW, T2, FW, T3))
    a123 = d('fsumadd', [ffw, c(PF['t1r'], T1), D(w, An, 'recnd', [D(w, An, 'readdcld', [PF['t2r'], PF['t3r']], '( %s + %s ) e. RR' % (T2, T3))], '( %s + %s ) e. CC' % (T2, T3))],
             'sum_ n e. %s %s = ( sum_ n e. %s %s + sum_ n e. %s ( %s + %s ) )' % (FW, PT, FW, T1, FW, T2, T3))
    # the three sums
    S1 = 'sum_ n e. %s %s' % (FW, BN('n')); S2 = 'sum_ n e. %s %s' % (FW, VMT('n', 'E')); S3 = 'sum_ n e. %s %s' % (FW, DT('n', K, '( E / 2 )'))
    m1 = d('fsummulc2', [ffw, d('recnd', [f4r], '%s e. CC' % F4), c(PF['bnr'], BN('n'))], '( %s x. %s ) = sum_ n e. %s %s' % (F4, S1, FW, T1))
    m2 = d('fsummulc2', [ffw, d('recnd', [lyr], '%s e. CC' % LY), c(PF['vr'], VMT('n', 'E'))], '( %s x. %s ) = sum_ n e. %s %s' % (LY, S2, FW, T2))
    m3 = d('fsummulc2', [ffw, d('recnd', [zer], '%s e. CC' % ZE), c(PF['dr'], DT('n', K, '( E / 2 )'))], '( %s x. %s ) = sum_ n e. %s %s' % (ZE, S3, FW, T3))
    flw = d('syl', [wz, w.inst('flid')], '( |_ ` W ) = W')
    np1 = use(w, A0, 'kd2npf', {'M': 'W'}, d('nnred', [wn], 'W e. RR'))
    np2 = d('eqbrtrrd', [d('sumeq1d', [d('oveq2d', [flw], '( 1 ... ( |_ ` W ) ) = %s' % FW)], 'sum_ n e. ( 1 ... ( |_ ` W ) ) %s = %s' % (BN('n'), S1)), np1], '%s <_ ; 2 0' % S1)
    fwnn = d('syl', [a1(w, A0, '1nn', '1 e. NN'), w.inst('fzssnn')], '%s C_ NN' % FW)
    vm = use(w, A0, 'kd2vmp', {'U': 'E', 'A': FW}, d('jca', [d('jca', [ep, linarith(w, A0, [e20], 'E <_ 1', closure=Closure(w, A0, {'E': ('RR', er)}))], '( E e. RR+ /\\ E <_ 1 )'),
                                                         d('jca', [ffw, fwnn], '( %s e. Fin /\\ %s C_ NN )' % (FW, FW))], '( ( E e. RR+ /\\ E <_ 1 ) /\\ ( %s e. Fin /\\ %s C_ NN ) )' % (FW, FW)))
    cbv = w.s([vmcong(w, 'n', 'k', 'E')], 'cbvsumv', '%s = sum_ k e. %s %s' % (S2, FW, VMT('k', 'E')))
    vm2 = d('eqbrtrd', [w.s([cbv], 'a1i', '( %s -> %s = sum_ k e. %s %s )' % (A0, S2, FW, VMT('k', 'E'))), vm], '%s <_ ( ( ( 5 / 4 ) / E ) + 5 )' % S2)
    cl40 = Closure(w, A0, {'E': ('RR', er)})
    e240 = linarith(w, A0, [e20], '( E / 2 ) <_ %s' % R120, closure=cl40)
    dg = use(w, A0, 'kd2dgp', {'U': '( E / 2 )', 'K': K, 'A': FW}, d('jca', [d('jca', [d('jca', [e2p, e240], '( ( E / 2 ) e. RR+ /\\ ( E / 2 ) <_ %s )' % R120), kn],
                                                                             '( ( ( E / 2 ) e. RR+ /\\ ( E / 2 ) <_ %s ) /\\ %s e. NN0 )' % (R120, K)), d('jca', [ffw, fwnn], '( %s e. Fin /\\ %s C_ NN )' % (FW, FW))],
                                                                     '( ( ( ( E / 2 ) e. RR+ /\\ ( E / 2 ) <_ %s ) /\\ %s e. NN0 ) /\\ ( %s e. Fin /\\ %s C_ NN ) )' % (R120, K, FW, FW)))
    cbd = w.s([dtcong(w, 'n', 'k', K, '( E / 2 )')], 'cbvsumv', '%s = sum_ k e. %s %s' % (S3, FW, DT('k', K, '( E / 2 )')))
    DG = DG2(K, '( E / 2 )')
    dg2 = d('eqbrtrd', [w.s([cbd], 'a1i', '( %s -> %s = sum_ k e. %s %s )' % (A0, S3, FW, DT('k', K, '( E / 2 )'))), dg], '%s <_ %s' % (S3, DG))
    s1r = d('fsumrecl', [ffw, PF['bnr']], '%s e. RR' % S1); s2r = d('fsumrecl', [ffw, PF['vr']], '%s e. RR' % S2); s3r = d('fsumrecl', [ffw, PF['dr']], '%s e. RR' % S3)
    clD = Closure(w, A0, {'E': ('RR+', ep), K: ('NN0', kn)})
    clD.leaf('( ! ` %s )' % K, 'RR+', d('nnrpd', [fnn], '( ! ` %s ) e. RR+' % K))
    clD.leaf('( exp ` 1 )', 'RR', d('rpred', [d('syl', [a1(w, A0, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR'))
    dgr = clD.mem(DG, 'RR')
    B54 = '( ( ( 5 / 4 ) / E ) + 5 )'
    l1 = d('lemul2ad', [s1r, w.s([num.real(w, '; 2 0')], 'a1i', '( %s -> ; 2 0 e. RR )' % A0), f4r, f40, np2], '( %s x. %s ) <_ ( %s x. ; 2 0 )' % (F4, S1, F4))
    l2 = d('lemul2ad', [s2r, clD.mem(B54, 'RR'), lyr, ly0, vm2], '( %s x. %s ) <_ ( %s x. %s )' % (LY, S2, LY, B54))
    l3 = d('lemul2ad', [s3r, dgr, zer, ze0, dg2], '( %s x. %s ) <_ ( %s x. %s )' % (ZE, S3, ZE, DG))
    # assemble
    SA = '( abs ` %s )' % SDF
    X_ = '( abs ` ( %s - %s ) )' % (SFW, DWIN('J', 'Y', 'Z'))
    xe = d('fveq2d', [df1], '%s = %s' % (X_, SA))
    atoms = {}
    Aa = [('( abs ` %s )' % SDF, d('abscld', [sdf], '( abs ` %s ) e. RR' % SDF)),
          ('sum_ n e. %s ( abs ` %s )' % (DF, a_('n')), d('fsumrecl', [ffdf, D(w, Adf, 'abscld', [ancdf], '( abs ` %s ) e. RR' % a_('n'))], 'sum_ n e. %s ( abs ` %s ) e. RR' % (DF, a_('n')))),
          ('sum_ n e. %s %s' % (DF, DT('n', K, 'E')), d('fsumrecl', [ffdf, dtr], 'sum_ n e. %s %s e. RR' % (DF, DT('n', K, 'E')))),
          ('sum_ n e. %s %s' % (DF, PT), d('fsumrecl', [ffdf, PD['pr']], 'sum_ n e. %s %s e. RR' % (DF, PT))),
          ('sum_ n e. %s %s' % (FW, PT), d('fsumrecl', [ffw, PF['pr']], 'sum_ n e. %s %s e. RR' % (FW, PT))),
          ('sum_ n e. %s %s' % (FW, T1), d('fsumrecl', [ffw, PF['t1r']], 'sum_ n e. %s %s e. RR' % (FW, T1))),
          ('sum_ n e. %s %s' % (FW, T2), d('fsumrecl', [ffw, PF['t2r']], 'sum_ n e. %s %s e. RR' % (FW, T2))),
          ('sum_ n e. %s %s' % (FW, T3), d('fsumrecl', [ffw, PF['t3r']], 'sum_ n e. %s %s e. RR' % (FW, T3))),
          ('sum_ n e. %s ( %s + %s )' % (FW, T2, T3), d('fsumrecl', [ffw, D(w, An, 'readdcld', [PF['t2r'], PF['t3r']], '( %s + %s ) e. RR' % (T2, T3))], 'sum_ n e. %s ( %s + %s ) e. RR' % (FW, T2, T3))),
          (S1, s1r), (S2, s2r), (S3, s3r), (F4, f4r), (LY, lyr), (ZE, zer), (DG, dgr), (B54, clD.mem(B54, 'RR')), (X_, d('abscld', [d('subcld', [d('fsumcl', [ffw, anc], '%s e. CC' % SFW),
                                                                                                                                              d('eqeltrd', [dw, sps], '%s e. CC' % DWIN('J', 'Y', 'Z'))], '( %s - %s ) e. CC' % (SFW, DWIN('J', 'Y', 'Z')))],
                                                                                                                               '%s e. RR' % X_))]
    clz = Closure(w, A0, {})
    for E_, st in Aa:
        clz.leaf(E_, 'RR', st)
    fin = nlinarith(w, A0, [xe, b1, b2, b3, b4, a123, a23, m1, m2, m3, l1, l2, l3], '%s <_ %s' % (X_, TL), closure=clz)
    w.qed([fin], 'idi', S['kd2psum'])
    return only_run(w, only)


def gen_sub():
    w = W('kd2sub', 'Lean ` KDerivDetect.norm_LSeries_sub_window_le ` with the three tails at the Metamath constants: ` abs ( LSK ( j + 1 , s0 ) - Dwin ) <_ 20 . 4^(j+1) (j+1)! + ( log X1 )^(j+1) ( ( 5 / 4 ) / eta + 5 ) + X2^(-eta/2) (j+1)! e ( 5 / 4 ) ( j + 3 ) / ( eta / 2 )^(j+2) ` (limit of ~ kd2psum ).')
    from kd2_c import ltcc
    A0 = SUBH
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    nxh = d('simp1', [], NXH); h2 = d('simp2', [], '( T e. RR /\\ E e. RR+ /\\ E <_ %s )' % R120); h3 = d('simp3', [], '( ( Y e. RR /\\ 1 <_ Y ) /\\ ( Z e. RR /\\ Y <_ Z ) /\\ J e. NN0 )')
    tr = d('simp1d', [h2], 'T e. RR'); ep = d('simp2d', [h2], 'E e. RR+'); e20 = d('simp3d', [h2], 'E <_ %s' % R120)
    gy = d('simp1d', [h3], '( Y e. RR /\\ 1 <_ Y )'); gz = d('simp2d', [h3], '( Z e. RR /\\ Y <_ Z )'); jn = d('simp3d', [h3], 'J e. NN0')
    yr = d('simpld', [gy], 'Y e. RR'); y1 = d('simprd', [gy], '1 <_ Y'); zr = d('simpld', [gz], 'Z e. RR'); yz = d('simprd', [gz], 'Y <_ Z')
    er = d('rpred', [ep], 'E e. RR')
    K = '( J + 1 )'; kn = d('syl', [jn, w.inst('peano2nn0')], '%s e. NN0' % K)
    S0T = S0()
    s0c = d('addcld', [d('recnd', [d('readdcld', [a1(w, A0, '1re', '1 e. RR'), er], '( 1 + E ) e. RR')], '( 1 + E ) e. CC'),
                       d('mulcld', [a1(w, A0, 'ax-icn', '_i e. CC'), d('recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % S0T)
    rs = d('syl2anc', [d('readdcld', [a1(w, A0, '1re', '1 e. RR'), er], '( 1 + E ) e. RR'), tr, w.inst('crre')], '( Re ` %s ) = ( 1 + E )' % S0T)
    e1 = linarith(w, A0, [e20], 'E <_ 1', closure=Closure(w, A0, {'E': ('RR', er)}))
    LSKH = d('3jca', [nxh, d('jca', [ep, e1], '( E e. RR+ /\\ E <_ 1 )'), d('3jca', [s0c, rs, kn], '( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ %s e. NN0 )' % (S0T, S0T, K))],
             '( %s /\\ ( E e. RR+ /\\ E <_ 1 ) /\\ ( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ %s e. NN0 ) )' % (NXH, S0T, S0T, K))
    kd = use(w, A0, 'kdlsb', {'K': K, 'S': S0T}, LSKH)
    kc = split_imp(tsub(stmt('kdlsb'), {'K': K, 'S': S0T}))[1]
    cvn = d('simpld', [kd], top_and(kc)[0])
    Fn = '( n e. NN |-> %s )' % LT(K, S0T, 'n'); Fm = '( m e. NN |-> %s )' % LT(K, S0T, 'm')
    ce = w.s([tcong(w, 'n', 'm', K, S0T)], 'cbvmptv', '%s = %s' % (Fn, Fm))
    cvm = d('mpbid', [cvn, w.s([w.s([w.s([ce, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (Fn, Fm))], 'eleq1i', '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (Fn, Fm))],
                              'a1i', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A0, Fn, Fm))], 'seq 1 ( + , %s ) e. dom ~~>' % Fm)
    SQ_ = 'seq 1 ( + , %s )' % Fm
    LS = LSK(K, S0T)
    An = '( %s /\\ n e. NN )' % A0
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    ltc = ltcc(w, An, 'n', nn_, lift(w, nxh, An), (lift(w, kn, An), K), (lift(w, s0c, An), S0T))
    mc = w.s([tcong(w, 'm', 'n', K, S0T)], 'adantl', '( ( %s /\\ m = n ) -> %s = %s )' % (An, LT(K, S0T, 'm'), LT(K, S0T, 'n')))
    fv = D(w, An, 'fvmptd', [a1(w, An, 'eqid', '%s = %s' % (Fm, Fm)), mc, nn_, ltc], '( %s ` n ) = %s' % (Fm, LT(K, S0T, 'n')))
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    cl1 = d('isumclim2', [nnu, a1(w, A0, '1z', '1 e. ZZ'), fv, ltc, cvm], '%s ~~> %s' % (SQ_, LS))
    # DW e. CC via kd2psum's own argument is not needed: DW is a finite sum
    PS = PSET('Y', 'Z')
    Ap = '( %s /\\ p e. %s )' % (A0, PS)
    pps = w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PS))
    pin = D(w, Ap, 'sseldd', [a1(w, Ap, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PS), pps], 'p e. ( 1 ... ( |_ ` Z ) )')
    pnn = D(w, Ap, 'syl', [pin, w.inst('elfznn')], 'p e. NN')
    pc = D(w, Ap, 'nncnd', [pnn], 'p e. CC')
    lg = D(w, Ap, 'recnd', [D(w, Ap, 'relogcld', [D(w, Ap, 'nnrpd', [pnn], 'p e. RR+')], '( log ` p ) e. RR')], '( log ` p ) e. CC')
    phc = D(w, Ap, 'mulcld', [D(w, Ap, 'expcld', [lg, lift(w, kn, Ap)], '( ( log ` p ) ^ %s ) e. CC' % K), D(w, Ap, 'cxpcld', [pc, D(w, Ap, 'negcld', [lift(w, d('recnd', [er], 'E e. CC'), Ap)], '-u E e. CC')], '( p ^c -u E ) e. CC')],
             '%s e. CC' % PHI('J', 'p'))
    cpc = D(w, Ap, 'mulcld', [D(w, Ap, 'mulcld', [D(w, Ap, 'syl2anc', [lift(w, nxh, Ap), pnn, w.inst('lchrcl')], '%s e. CC' % CHV('p')), lg], '( %s x. ( log ` p ) ) e. CC' % CHV('p')),
                              D(w, Ap, 'cxpcld', [pc, D(w, Ap, 'subcld', [D(w, Ap, 'negcld', [a1(w, Ap, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'),
                                                                          D(w, Ap, 'mulcld', [D(w, Ap, 'recnd', [lift(w, tr, Ap)], 'T e. CC'), a1(w, Ap, 'ax-icn', '_i e. CC')], '( T x. _i ) e. CC')],
                                                     '( -u 1 - ( T x. _i ) ) e. CC')], '( p ^c ( -u 1 - ( T x. _i ) ) ) e. CC')], '%s e. CC' % CP('p'))
    DW = DWIN('J', 'Y', 'Z')
    dwc = d('fsumcl', [d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` Z ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PS)], '%s e. Fin' % PS),
                       D(w, Ap, 'mulcld', [phc, cpc], '( %s x. %s ) e. CC' % (PHI('J', 'p'), CP('p')))], '%s e. CC' % DW)
    # G = seq - DW, H = abs G
    G = '( x e. NN |-> ( ( %s ` x ) - %s ) )' % (SQ_, DW)
    H = '( x e. NN |-> ( abs ` ( ( %s ` x ) - %s ) ) )' % (SQ_, DW)
    # seq values are complex
    Ak = '( %s /\\ k e. NN )' % A0
    kk = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    Akn = '( %s /\\ n e. ( 1 ... k ) )' % Ak
    nk = D(w, Akn, 'syl', [w.s([], 'simpr', '( %s -> n e. ( 1 ... k ) )' % Akn), w.inst('elfznn')], 'n e. NN')
    ltck = ltcc(w, Akn, 'n', nk, lift(w, nxh, Akn), (lift(w, kn, Akn), K), (lift(w, s0c, Akn), S0T))
    mck = w.s([tcong(w, 'm', 'n', K, S0T)], 'adantl', '( ( %s /\\ m = n ) -> %s = %s )' % (Akn, LT(K, S0T, 'm'), LT(K, S0T, 'n')))
    fvk = D(w, Akn, 'fvmptd', [a1(w, Akn, 'eqid', '%s = %s' % (Fm, Fm)), mck, nk, ltck], '( %s ` n ) = %s' % (Fm, LT(K, S0T, 'n')))
    ku = D(w, Ak, 'mpbid', [kk, a1(w, Ak, 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'k e. ( ZZ>= ` 1 )')
    fs = D(w, Ak, 'fsumser', [fvk, ku, ltck], 'sum_ n e. ( 1 ... k ) %s = ( %s ` k )' % (LT(K, S0T, 'n'), SQ_))
    sqc = D(w, Ak, 'eqeltrrd', [fs, D(w, Ak, 'fsumcl', [D(w, Ak, 'fzfid', [], '( 1 ... k ) e. Fin'), ltck], 'sum_ n e. ( 1 ... k ) %s e. CC' % LT(K, S0T, 'n'))], '( %s ` k ) e. CC' % SQ_)
    xg = w.s([w.s([], 'fveq2', '( x = k -> ( %s ` x ) = ( %s ` k ) )' % (SQ_, SQ_))], 'oveq1d', '( x = k -> ( ( %s ` x ) - %s ) = ( ( %s ` k ) - %s ) )' % (SQ_, DW, SQ_, DW))
    gv = D(w, Ak, 'fvmptd', [a1(w, Ak, 'eqid', '%s = %s' % (G, G)), w.s([xg], 'adantl', '( ( %s /\\ x = k ) -> ( ( %s ` x ) - %s ) = ( ( %s ` k ) - %s ) )' % (Ak, SQ_, DW, SQ_, DW)), kk,
                             D(w, Ak, 'subcld', [sqc, lift(w, dwc, Ak)], '( ( %s ` k ) - %s ) e. CC' % (SQ_, DW))], '( %s ` k ) = ( ( %s ` k ) - %s )' % (G, SQ_, DW))
    nnx = a1(w, A0, 'nnex', 'NN e. _V')
    gex = d('mptexd', [nnx], '%s e. _V' % G); hex_ = d('mptexd', [nnx], '%s e. _V' % H)
    cg = d('climsubc1', [nnu, a1(w, A0, '1z', '1 e. ZZ'), cl1, dwc, gex, sqc, gv], '%s ~~> ( %s - %s )' % (G, LS, DW))
    xh = w.s([xg], 'fveq2d', '( x = k -> ( abs ` ( ( %s ` x ) - %s ) ) = ( abs ` ( ( %s ` k ) - %s ) ) )' % (SQ_, DW, SQ_, DW))
    hv = D(w, Ak, 'fvmptd', [a1(w, Ak, 'eqid', '%s = %s' % (H, H)), w.s([xh], 'adantl', '( ( %s /\\ x = k ) -> ( abs ` ( ( %s ` x ) - %s ) ) = ( abs ` ( ( %s ` k ) - %s ) ) )' % (Ak, SQ_, DW, SQ_, DW)), kk,
                             D(w, Ak, 'abscld', [D(w, Ak, 'subcld', [sqc, lift(w, dwc, Ak)], '( ( %s ` k ) - %s ) e. CC' % (SQ_, DW))], '( abs ` ( ( %s ` k ) - %s ) ) e. RR' % (SQ_, DW))],
            '( %s ` k ) = ( abs ` ( ( %s ` k ) - %s ) )' % (H, SQ_, DW))
    hv2 = D(w, Ak, 'eqtr4d', [hv, D(w, Ak, 'fveq2d', [gv], '( abs ` ( %s ` k ) ) = ( abs ` ( ( %s ` k ) - %s ) )' % (G, SQ_, DW))], '( %s ` k ) = ( abs ` ( %s ` k ) )' % (H, G))
    gkc = D(w, Ak, 'eqeltrd', [gv, D(w, Ak, 'subcld', [sqc, lift(w, dwc, Ak)], '( ( %s ` k ) - %s ) e. CC' % (SQ_, DW))], '( %s ` k ) e. CC' % G)
    ch = d('climabs', [nnu, cg, hex_, a1(w, A0, '1z', '1 e. ZZ'), gkc, hv2], '%s ~~> ( abs ` ( %s - %s ) )' % (H, LS, DW))
    # climlec3 on ZZ>= |_ Z
    FZ = '( |_ ` Z )'
    fzn = d('syl2anc', [zr, d('letrd', [a1(w, A0, '1re', '1 e. RR'), yr, zr, y1, yz], '1 <_ Z'), w.inst('flge1nn')], '%s e. NN' % FZ)
    Au = '( %s /\\ k e. ( ZZ>= ` %s ) )' % (A0, FZ)
    ku_ = w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` %s ) )' % (Au, FZ))
    kun = D(w, Au, 'syl2anc', [lift(w, fzn, Au), ku_, w.inst('eluznn')], 'k e. NN')
    kle = D(w, Au, 'syl', [ku_, w.inst('eluzle')], '%s <_ k' % FZ)
    ps = use(w, Au, 'kd2psum', {'W': 'k'}, D(w, Au, 'jca', [lift(w, w.s([], 'id', '( %s -> %s )' % (A0, A0)), Au), D(w, Au, 'jca', [kun, kle], '( k e. NN /\\ %s <_ k )' % FZ)],
                                                        '( %s /\\ ( k e. NN /\\ %s <_ k ) )' % (A0, FZ)))
    # rewrite the partial sum as the seq value and H ` k
    Akk = '( %s /\\ k e. NN )' % A0
    fs2 = w.s([w.s([fs], 'ex', '( %s -> ( k e. NN -> sum_ n e. ( 1 ... k ) %s = ( %s ` k ) ) )' % (A0, LT(K, S0T, 'n'), SQ_))], 'idi', '( %s -> ( k e. NN -> sum_ n e. ( 1 ... k ) %s = ( %s ` k ) ) )' % (A0, LT(K, S0T, 'n'), SQ_))
    fsu = D(w, Au, 'mpd', [kun, lift(w, fs2, Au)], 'sum_ n e. ( 1 ... k ) %s = ( %s ` k )' % (LT(K, S0T, 'n'), SQ_))
    hvs = w.s([hv], 'ex', '( %s -> ( k e. NN -> ( %s ` k ) = ( abs ` ( ( %s ` k ) - %s ) ) ) )' % (A0, H, SQ_, DW))
    hvu = D(w, Au, 'mpd', [kun, lift(w, hvs, Au)], '( %s ` k ) = ( abs ` ( ( %s ` k ) - %s ) )' % (H, SQ_, DW))
    PSK = 'sum_ n e. ( 1 ... k ) %s' % LT(K, S0T, 'n')
    hle = D(w, Au, 'breqtrd' if False else 'eqbrtrd', [D(w, Au, 'eqtr4d', [hvu, D(w, Au, 'fveq2d', [D(w, Au, 'oveq1d', [fsu], '( %s - %s ) = ( ( %s ` k ) - %s )' % (PSK, DW, SQ_, DW))],
                                                                                 '( abs ` ( %s - %s ) ) = ( abs ` ( ( %s ` k ) - %s ) )' % (PSK, DW, SQ_, DW))],
                                                        '( %s ` k ) = ( abs ` ( %s - %s ) )' % (H, PSK, DW)), ps], '( %s ` k ) <_ %s' % (H, TL))
    hre = D(w, Au, 'eqeltrd', [hvu, D(w, Au, 'abscld', [D(w, Au, 'subcld', [D(w, Au, 'mpd', [kun, lift(w, w.s([sqc], 'ex', '( %s -> ( k e. NN -> ( %s ` k ) e. CC ) )' % (A0, SQ_)), Au)], '( %s ` k ) e. CC' % SQ_),
                                                                       lift(w, dwc, Au)], '( ( %s ` k ) - %s ) e. CC' % (SQ_, DW))], '( abs ` ( ( %s ` k ) - %s ) ) e. RR' % (SQ_, DW))],
               '( %s ` k ) e. RR' % H)
    cl = Closure(w, A0, {'E': ('RR+', ep), K: ('NN0', kn), 'Y': ('RR', yr), 'Z': ('RR', zr)})
    ypp = d('elrpd', [yr, linarith(w, A0, [y1], '0 < Y', closure=Closure(w, A0, {'Y': ('RR', yr)}))], 'Y e. RR+')
    zpp = d('elrpd', [zr, linarith(w, A0, [y1, yz], '0 < Z', closure=Closure(w, A0, {'Y': ('RR', yr), 'Z': ('RR', zr)}))], 'Z e. RR+')
    cl.leaf('Y', 'RR+', ypp); cl.leaf('Z', 'RR+', zpp)
    cl.leaf('( ! ` %s )' % K, 'RR+', d('nnrpd', [d('faccld', [kn], '( ! ` %s ) e. NN' % K)], '( ! ` %s ) e. RR+' % K))
    cl.leaf('( exp ` 1 )', 'RR', d('rpred', [d('syl', [a1(w, A0, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR'))
    cl.leaf('( log ` Y )', 'RR', d('relogcld', [ypp], '( log ` Y ) e. RR'))
    cl.leaf('( Z ^c -u ( E / 2 ) )', 'RR', d('rpred', [d('rpcxpcld', [zpp, cl.mem('-u ( E / 2 )', 'RR')], '( Z ^c -u ( E / 2 ) ) e. RR+')], '( Z ^c -u ( E / 2 ) ) e. RR'))
    UZ = '( ZZ>= ` %s )' % FZ
    CST = '( %s X. { %s } )' % (UZ, TL)
    tlr = cl.mem(TL, 'RR')
    fzz = d('nnzd', [fzn], '%s e. ZZ' % FZ)
    cc_ = d('syl2anc', [d('recnd', [tlr], '%s e. CC' % TL), fzz, w.s([w.s([], 'ssid', '%s C_ %s' % (UZ, UZ)), w.s([], 'fvex', '%s e. _V' % UZ)], 'climconst2', '( ( %s e. CC /\\ %s e. ZZ ) -> %s ~~> %s )' % (TL, FZ, CST, TL))],
            '%s ~~> %s' % (CST, TL))
    fvc = w.s([w.s([w.s([], 'ovex', '%s e. _V' % TL)], 'fvconst2', '( k e. %s -> ( %s ` k ) = %s )' % (UZ, CST, TL))], 'adantl', '( %s -> ( %s ` k ) = %s )' % (Au, CST, TL))
    cre = D(w, Au, 'eqeltrd', [fvc, lift(w, tlr, Au)], '( %s ` k ) e. RR' % CST)
    hle2 = D(w, Au, 'breqtrrd', [hle, fvc], '( %s ` k ) <_ ( %s ` k )' % (H, CST))
    fin = d('climle', [w.s([], 'eqid', '%s = %s' % (UZ, UZ)), fzz, ch, cc_, hre, cre, hle2], '( abs ` ( %s - %s ) ) <_ %s' % (LS, DW, TL))
    w.qed([fin], 'idi', S['kd2sub'])
    return only_run(w, only)


if __name__ == '__main__':
    gen_vmp()
    gen_npf()
    gen_pwt()
    gen_pt()
    gen_dgp()
    gen_psum()
    gen_sub()
