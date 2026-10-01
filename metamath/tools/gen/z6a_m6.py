"""Z6a (block D): the Mellin identity (z6mtel, z6malg3, z6mhalf, z6mellin, z6mg32, z6mtail)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_mlib import *
from tm import sub

only = sys.argv[1:]
H = '( 1 / 2 )'
ALn = lambda n: '( -u %s - ( 1 / 2 ) )' % n
ESUM = lambda n: 'sum_ k e. ( 0 ... %s ) ( ( -u Y ^ k ) / ( ! ` k ) )' % n
RT = lambda n: '( ( -u Y ^ %s ) / ( ! ` %s ) )' % (n, n)
VLH = VL(GYM, H)
VLn = lambda n: VL(GYM, ALn(n))
EY = '( %s x. ( exp ` -u Y ) )' % TPI


def want(lab):
    return not only or lab in only


def tpic(w, A):
    s = mkst(w, A)
    return s([a1c(w, A, '2cn', '2 e. CC'), s([a1c(w, A, 'ax-icn', '_i e. CC'), a1c(w, A, 'picn', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)


def vlhc(w, A, yrp):
    """( A -> VL(GY,1/2) e. CC )"""
    s = mkst(w, A)
    hr = a1c(w, A, 'halfre', '%s e. RR' % H)
    a = s([yrp, s([hr, s([s([hr], 'leidd', '%s <_ %s' % (H, H)), w.s([num.le_lit(w, H, '3')], 'a1i', '( %s -> %s <_ 3 )' % (A, H))], 'jca', '( %s <_ %s /\\ %s <_ 3 )' % (H, H, H))],
                       'jca', '( %s e. RR /\\ ( %s <_ %s /\\ %s <_ 3 ) )' % (H, H, H, H))], 'jca', '( Y e. RR+ /\\ ( %s e. RR /\\ ( %s <_ %s /\\ %s <_ 3 ) ) )' % (H, H, H, H))
    l = s([a, w.inst('z6mvlr')], 'syl', '%s ~~>r %s' % (VLF(GYM, H), VLH))
    return s([l, w.inst('rlimcl')], 'syl', '%s e. CC' % VLH)


def vlnc(w, A, yrp, nn, n):
    s = mkst(w, A)
    l = s([s([yrp, nn], 'jca', '( Y e. RR+ /\\ %s e. NN0 )' % n), w.inst('z6mvll')], 'syl', '%s ~~>r %s' % (VLF(GYM, ALn(n)), VLn(n)))
    return s([l, w.inst('rlimcl')], 'syl', '%s e. CC' % VLn(n))


def rtc(w, A, yrp, nn, n):
    """( A -> ( ( -u Y ^ n ) / ( ! ` n ) ) e. CC )"""
    s = mkst(w, A)
    fn = s([nn, w.inst('faccl')], 'syl', '( ! ` %s ) e. NN' % n)
    return s([s([s([s([yrp], 'rpcnd', 'Y e. CC')], 'negcld', '-u Y e. CC'), nn], 'expcld', '( -u Y ^ %s ) e. CC' % n), s([fn], 'nncnd', '( ! ` %s ) e. CC' % n),
              s([fn], 'nnne0d', '( ! ` %s ) =/= 0' % n)], 'divcld', '%s e. CC' % RT(n))


def esumc(w, A, yrp, nn, n):
    """( A -> ESUM(n) e. CC ) by fsumcl (A must not contain k)"""
    Ak = '( %s /\\ k e. ( 0 ... %s ) )' % (A, n)
    kk = w.s([w.s([], 'simpr', '( %s -> k e. ( 0 ... %s ) )' % (Ak, n)), w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % Ak)
    tc = rtc(w, Ak, lift(w, yrp, Ak), kk, 'k')
    return w.s([a1c(w, A, 'fzfi', '( 0 ... %s ) e. Fin' % n), tc], 'fsumcl', '( %s -> %s e. CC )' % (A, ESUM(n)))


# ---------------------------------------------------------------- z6mtel
def z6mtel():
    w = W('z6mtel', 'The residues telescope: ` VL ( 1 / 2 ) = VL ( -u K - 1 / 2 ) + 2 pi i sum_ k <_ K ( -u Y ) ^ k / k ! ` '
          '(induction on ` K ` with ~ z6mstep ; ~ fsump1 ).')
    P = lambda n: '( Y e. RR+ -> %s = ( %s + ( %s x. %s ) ) )' % (VLH, VLn(n), TPI, ESUM(n))

    def sb(T):
        idk = w.s([], 'id', '( n = %s -> n = %s )' % (T, T))
        stp, new = w.wcongr(P('n'), {'n': T}, 'n = %s' % T, {'n': idk})
        assert new == P(T), new
        return stp
    h1 = sb('0'); h2 = sb('m'); h3 = sb('( m + 1 )'); h4 = sb('K')
    # base
    A0 = 'Y e. RR+'
    s = mkst(w, A0)
    yrp = w.s([], 'id', '( Y e. RR+ -> Y e. RR+ )')
    n0 = a1c(w, A0, '0nn0', '0 e. NN0')
    ms = s([s([yrp, n0], 'jca', '( Y e. RR+ /\\ 0 e. NN0 )'), w.inst('z6mstep')], 'syl',
           '( %s - %s ) = ( %s x. %s )' % (VL(GYM, '( %s - 0 )' % H), VLn('0'), TPI, RT('0')))
    h0 = a1(w, A0, w.s([w.s([], 'halfcn', '%s e. CC' % H)], 'subid1i', '( %s - 0 ) = %s' % (H, H)), '( %s - 0 ) = %s' % (H, H))
    rw, new = w.rewrite(VL(GYM, '( %s - 0 )' % H), {'( %s - 0 )' % H: (H, h0)}, A0)
    assert new == VLH
    ms2 = s([s([rw], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (VL(GYM, '( %s - 0 )' % H), VLn('0'), VLH, VLn('0'))), ms], 'eqtr3d',
            '( %s - %s ) = ( %s x. %s )' % (VLH, VLn('0'), TPI, RT('0')))
    t0 = s([tpic(w, A0), rtc(w, A0, yrp, n0, '0')], 'mulcld', '( %s x. %s ) e. CC' % (TPI, RT('0')))
    sa = s([vlhc(w, A0, yrp), vlnc(w, A0, yrp, n0, '0'), t0, ], 'subaddd', '( ( %s - %s ) = ( %s x. %s ) <-> ( %s + ( %s x. %s ) ) = %s )' % (VLH, VLn('0'), TPI, RT('0'), VLn('0'), TPI, RT('0'), VLH))
    b1 = s([s([ms2, sa], 'mpbid', '( %s + ( %s x. %s ) ) = %s' % (VLn('0'), TPI, RT('0'), VLH))], 'eqcomd', '%s = ( %s + ( %s x. %s ) )' % (VLH, VLn('0'), TPI, RT('0')))
    idk = w.s([], 'id', '( k = 0 -> k = 0 )')
    sb0, v0 = w.congr('( ( -u Y ^ k ) / ( ! ` k ) )', {'k': '0'}, 'k = 0', {'k': idk})
    assert v0 == RT('0')
    f1 = s([a1c(w, A0, '0z', '0 e. ZZ'), rtc(w, A0, yrp, n0, '0'), w.s([sb0], 'fsum1', '( ( 0 e. ZZ /\\ %s e. CC ) -> %s = %s )' % (RT('0'), ESUM('0'), RT('0')))], 'syl2anc',
           '%s = %s' % (ESUM('0'), RT('0')))
    b2 = s([b1, s([s([s([f1], 'eqcomd', '%s = %s' % (RT('0'), ESUM('0')))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (TPI, RT('0'), TPI, ESUM('0')))], 'oveq2d',
                  '( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) )' % (VLn('0'), TPI, RT('0'), VLn('0'), TPI, ESUM('0')))], 'eqtrd', '%s = ( %s + ( %s x. %s ) )' % (VLH, VLn('0'), TPI, ESUM('0')))
    base = b2
    # step
    M1 = '( m + 1 )'
    A = '( ( m e. NN0 /\\ %s ) /\\ Y e. RR+ )' % P('m')
    s = mkst(w, A)
    mn = w.s([], 'simpll', '( %s -> m e. NN0 )' % A)
    yrp = w.s([], 'simpr', '( %s -> Y e. RR+ )' % A)
    ih = s([yrp, w.s([], 'simplr', '( %s -> %s )' % (A, P('m')))], 'mpd', '%s = ( %s + ( %s x. %s ) )' % (VLH, VLn('m'), TPI, ESUM('m')))
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '%s e. NN0' % M1)
    ms = s([s([yrp, m1n], 'jca', '( Y e. RR+ /\\ %s e. NN0 )' % M1), w.inst('z6mstep')], 'syl',
           '( %s - %s ) = ( %s x. %s )' % (VL(GYM, '( %s - %s )' % (H, M1)), VLn(M1), TPI, RT(M1)))
    mr = s([mn], 'nn0red', 'm e. RR')
    Am = 'm e. NN0'
    le = lineq(w, Am, '( %s - %s )' % (H, M1), ALn('m'), leaves={'m': w.s([w.s([], 'id', '( m e. NN0 -> m e. NN0 )')], 'nn0red', '( m e. NN0 -> m e. RR )')})
    rw0, new = w.rewrite(VL(GYM, '( %s - %s )' % (H, M1)), {'( %s - %s )' % (H, M1): (ALn('m'), le)}, Am)
    assert new == VLn('m')
    rw = s([mn, rw0], 'syl', '%s = %s' % (VL(GYM, '( %s - %s )' % (H, M1)), VLn('m')))
    ms2 = s([s([rw], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (VL(GYM, '( %s - %s )' % (H, M1)), VLn(M1), VLn('m'), VLn(M1))), ms], 'eqtr3d',
            '( %s - %s ) = ( %s x. %s )' % (VLn('m'), VLn(M1), TPI, RT(M1)))
    TR = '( %s x. %s )' % (TPI, RT(M1)); TS = '( %s x. %s )' % (TPI, ESUM('m'))
    tp = tpic(w, A)
    trc = s([tp, rtc(w, A, yrp, m1n, M1)], 'mulcld', '%s e. CC' % TR)
    vmc = vlnc(w, A, yrp, mn, 'm'); vm1c = vlnc(w, A, yrp, m1n, M1)
    sa = s([vmc, vm1c, trc], 'subaddd', '( ( %s - %s ) = %s <-> ( %s + %s ) = %s )' % (VLn('m'), VLn(M1), TR, VLn(M1), TR, VLn('m')))
    vm = s([s([ms2, sa], 'mpbid', '( %s + %s ) = %s' % (VLn(M1), TR, VLn('m')))], 'eqcomd', '%s = ( %s + %s )' % (VLn('m'), VLn(M1), TR))
    # the sum at m + 1 (under a k-free antecedent)
    A2 = '( Y e. RR+ /\\ m e. NN0 )'
    s2 = mkst(w, A2)
    y2 = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A2); m2 = w.s([], 'simpr', '( %s -> m e. NN0 )' % A2)
    uz = w.s([m2, w.s([], 'elnn0uz', '( m e. NN0 <-> m e. ( ZZ>= ` 0 ) )')], 'sylib', '( %s -> m e. ( ZZ>= ` 0 ) )' % A2)
    Ak = '( %s /\\ k e. ( 0 ... %s ) )' % (A2, M1)
    kk = w.s([w.s([], 'simpr', '( %s -> k e. ( 0 ... %s ) )' % (Ak, M1)), w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % Ak)
    tk = rtc(w, Ak, lift(w, y2, Ak), kk, 'k')
    idk = w.s([], 'id', '( k = %s -> k = %s )' % (M1, M1))
    sbk, vk = w.congr('( ( -u Y ^ k ) / ( ! ` k ) )', {'k': M1}, 'k = %s' % M1, {'k': idk})
    assert vk == RT(M1)
    fp = w.s([uz, tk, sbk], 'fsump1', '( %s -> %s = ( %s + %s ) )' % (A2, ESUM(M1), ESUM('m'), RT(M1)))
    fpA = s([yrp, mn, fp], 'syl2anc', '%s = ( %s + %s )' % (ESUM(M1), ESUM('m'), RT(M1)))
    sm = esumc(w, A2, y2, m2, 'm')
    smA = s([yrp, mn, sm], 'syl2anc', '%s e. CC' % ESUM('m'))
    tsc = s([tp, smA], 'mulcld', '%s e. CC' % TS)
    e1 = s([ih, s([vm], 'oveq1d', '( %s + %s ) = ( ( %s + %s ) + %s )' % (VLn('m'), TS, VLn(M1), TR, TS))], 'eqtrd', '%s = ( ( %s + %s ) + %s )' % (VLH, VLn(M1), TR, TS))
    e2 = s([vm1c, trc, tsc], 'addassd', '( ( %s + %s ) + %s ) = ( %s + ( %s + %s ) )' % (VLn(M1), TR, TS, VLn(M1), TR, TS))
    e3 = s([trc, tsc], 'addcomd', '( %s + %s ) = ( %s + %s )' % (TR, TS, TS, TR))
    e4 = s([tp, smA, rtc(w, A, yrp, m1n, M1)], 'adddid', '( %s x. ( %s + %s ) ) = ( %s + %s )' % (TPI, ESUM('m'), RT(M1), TS, TR))
    e5 = s([s([fpA], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s + %s ) )' % (TPI, ESUM(M1), TPI, ESUM('m'), RT(M1))), e4], 'eqtrd',
           '( %s x. %s ) = ( %s + %s )' % (TPI, ESUM(M1), TS, TR))
    e6 = s([e3, e5], 'eqtr4d', '( %s + %s ) = ( %s x. %s )' % (TR, TS, TPI, ESUM(M1)))
    fin = s([s([e1, e2], 'eqtrd', '%s = ( %s + ( %s + %s ) )' % (VLH, VLn(M1), TR, TS)), s([e6], 'oveq2d', '( %s + ( %s + %s ) ) = ( %s + ( %s x. %s ) )' % (VLn(M1), TR, TS, VLn(M1), TPI, ESUM(M1)))],
            'eqtrd', '%s = ( %s + ( %s x. %s ) )' % (VLH, VLn(M1), TPI, ESUM(M1)))
    e7 = w.s([fin], 'ex', '( ( m e. NN0 /\\ %s ) -> %s )' % (P('m'), P(M1)))
    e8 = w.s([e7], 'ex', '( m e. NN0 -> ( %s -> %s ) )' % (P('m'), P(M1)))
    ind = w.s([h1, h2, h3, h4, base, e8], 'nn0ind', '( K e. NN0 -> %s )' % P('K'))
    w.qed([ind], 'impcom', STATEMENTS['z6mtel'])
    return w


# ---------------------------------------------------------------- z6malg3
def z6malg3():
    w = W('z6malg3', 'Field algebra: ` ( ( 2 ( P Q ) / F ) G = ( ( 2 Q ) G ) ( P / F ) ` .')
    A = split_imp(STATEMENTS['z6malg3'])[0]
    s = mkst(w, A)
    pc = w.s([], 'simp1l', '( %s -> P e. CC )' % A); qc = w.s([], 'simp1r', '( %s -> Q e. CC )' % A)
    fc = w.s([], 'simp2l', '( %s -> F e. CC )' % A); fn = w.s([], 'simp2r', '( %s -> F =/= 0 )' % A)
    gc = w.s([], 'simp3', '( %s -> G e. CC )' % A)
    tc = a1c(w, A, '2cn', '2 e. CC')
    q2 = s([tc, qc], 'mulcld', '( 2 x. Q ) e. CC')
    e1 = s([s([tc, pc, qc], 'mul12d', '( 2 x. ( P x. Q ) ) = ( P x. ( 2 x. Q ) )'), s([pc, q2], 'mulcomd', '( P x. ( 2 x. Q ) ) = ( ( 2 x. Q ) x. P )')], 'eqtrd',
           '( 2 x. ( P x. Q ) ) = ( ( 2 x. Q ) x. P )')
    e2 = s([s([e1], 'oveq1d', '( ( 2 x. ( P x. Q ) ) / F ) = ( ( ( 2 x. Q ) x. P ) / F )'), s([q2, pc, fc, fn], 'divassd', '( ( ( 2 x. Q ) x. P ) / F ) = ( ( 2 x. Q ) x. ( P / F ) )')],
           'eqtrd', '( ( 2 x. ( P x. Q ) ) / F ) = ( ( 2 x. Q ) x. ( P / F ) )')
    e3 = s([s([e2], 'oveq1d', '( ( ( 2 x. ( P x. Q ) ) / F ) x. G ) = ( ( ( 2 x. Q ) x. ( P / F ) ) x. G )'),
            s([q2, s([pc, fc, fn], 'divcld', '( P / F ) e. CC'), gc], 'mul32d', '( ( ( 2 x. Q ) x. ( P / F ) ) x. G ) = ( ( ( 2 x. Q ) x. G ) x. ( P / F ) )')],
           'eqtrd', '( ( ( 2 x. ( P x. Q ) ) / F ) x. G ) = ( ( ( 2 x. Q ) x. G ) x. ( P / F ) )')
    toqed(w, e3, 'z6malg3')
    return w


# ---------------------------------------------------------------- z6mhalf
def z6mhalf():
    w = W('z6mhalf', 'The Mellin identity on ` Re w = 1 / 2 ` : ` VL ( 1 / 2 ) = 2 pi i e ^ -u Y ` .  By ~ z6mtel , '
          '` | VL ( 1 / 2 ) - 2 pi i sum_ k <_ K ( -u Y ) ^ k / k ! | = | VL ( -u K - 1 / 2 ) | <_ c Y ^ K / K ! ` ( ~ z6mleft ); '
          'the partial sums tend to ` e ^ -u Y ` ( ~ efcvgfsum ), the bound to ` 0 ` ( ~ efcvg , ~ serf0 ), and ~ climle .')
    A = 'Y e. RR+'
    s = mkst(w, A)
    yrp = w.s([], 'id', '( Y e. RR+ -> Y e. RR+ )')
    yc = s([yrp], 'rpcnd', 'Y e. CC')
    V = VLH
    vc = vlhc(w, A, yrp)
    tp = tpic(w, A)
    ec = s([tp, s([s([yc], 'negcld', '-u Y e. CC'), w.inst('efcl')], 'syl', '( exp ` -u Y ) e. CC')], 'mulcld', '%s e. CC' % EY)
    ESn = ESUM('n')
    Fs = '( n e. NN0 |-> %s )' % ESn
    Gm = '( n e. NN0 |-> ( %s x. %s ) )' % (TPI, ESn)
    G1 = '( n e. NN0 |-> ( %s - ( %s x. %s ) ) )' % (V, TPI, ESn)
    Ab = '( n e. NN0 |-> ( abs ` ( %s - ( %s x. %s ) ) ) )' % (V, TPI, ESn)
    Tm = '( n e. NN0 |-> ( ( Y ^ n ) / ( ! ` n ) ) )'
    c0 = '( ( 2 x. ( Y ^c ( 1 / 2 ) ) ) x. %s )' % KG
    Bd = '( n e. NN0 |-> ( %s x. ( ( Y ^ n ) / ( ! ` n ) ) ) )' % c0
    nu = w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
    z0 = a1c(w, A, '0z', '0 e. ZZ')
    nn0v = w.s([], 'nn0ex', 'NN0 e. _V')
    ex = lambda M: a1(w, A, w.s([nn0v], 'mptex', '%s e. _V' % M), '%s e. _V' % M)
    Aj = '( %s /\\ j e. NN0 )' % A
    t = mkst(w, Aj)
    jm = w.s([], 'simpr', '( %s -> j e. NN0 )' % Aj)
    yj = w.s([], 'simpl', '( %s -> Y e. RR+ )' % Aj)
    fsv, _ = mpval(w, Aj, 'n', 'NN0', ESn, 'j', jm, exs=a1(w, Aj, w.s([], 'sumex', '%s e. _V' % ESUM('j')), '%s e. _V' % ESUM('j')))
    gmv, _ = mpval(w, Aj, 'n', 'NN0', '( %s x. %s )' % (TPI, ESn), 'j', jm)
    g1v, _ = mpval(w, Aj, 'n', 'NN0', '( %s - ( %s x. %s ) )' % (V, TPI, ESn), 'j', jm)
    abv, _ = mpval(w, Aj, 'n', 'NN0', '( abs ` ( %s - ( %s x. %s ) ) )' % (V, TPI, ESn), 'j', jm)
    tmv, _ = mpval(w, Aj, 'n', 'NN0', '( ( Y ^ n ) / ( ! ` n ) )', 'j', jm)
    bdv, _ = mpval(w, Aj, 'n', 'NN0', '( %s x. ( ( Y ^ n ) / ( ! ` n ) ) )' % c0, 'j', jm)
    ej = esumc(w, Aj, yj, jm, 'j')
    tpj = lift(w, tp, Aj)
    fsc = t([fsv, ej], 'eqeltrd', '( %s ` j ) e. CC' % Fs)
    tsj = t([tpj, ej], 'mulcld', '( %s x. %s ) e. CC' % (TPI, ESUM('j')))
    gmc = t([gmv, tsj], 'eqeltrd', '( %s ` j ) e. CC' % Gm)
    dj = t([lift(w, vc, Aj), tsj], 'subcld', '( %s - ( %s x. %s ) ) e. CC' % (V, TPI, ESUM('j')))
    g1c = t([g1v, dj], 'eqeltrd', '( %s ` j ) e. CC' % G1)
    fnj = t([jm, w.inst('faccl')], 'syl', '( ! ` j ) e. NN')
    tmj = t([t([t([yj], 'rpcnd', 'Y e. CC'), jm], 'expcld', '( Y ^ j ) e. CC'), t([fnj], 'nncnd', '( ! ` j ) e. CC'), t([fnj], 'nnne0d', '( ! ` j ) =/= 0')], 'divcld',
            '( ( Y ^ j ) / ( ! ` j ) ) e. CC')
    tmc = t([tmv, tmj], 'eqeltrd', '( %s ` j ) e. CC' % Tm)
    # 1. the partial sums
    efs = s([s([yc], 'negcld', '-u Y e. CC'), w.s([w.s([], 'eqid', '%s = %s' % (Fs, Fs))], 'efcvgfsum', '( -u Y e. CC -> %s ~~> ( exp ` -u Y ) )' % Fs)], 'syl',
            '%s ~~> ( exp ` -u Y )' % Fs)
    mc = w.s([nu, z0, efs, tp, ex(Gm), fsc, t([gmv, t([fsv], 'oveq2d', '( %s x. ( %s ` j ) ) = ( %s x. %s )' % (TPI, Fs, TPI, ESUM('j')))], 'eqtr4d',
                                                    '( %s ` j ) = ( %s x. ( %s ` j ) )' % (Gm, TPI, Fs))], 'climmulc2', '( %s -> %s ~~> %s )' % (A, Gm, EY))
    sc = w.s([nu, z0, mc, vc, ex(G1), gmc, t([g1v, t([gmv], 'oveq2d', '( %s - ( %s ` j ) ) = ( %s - ( %s x. %s ) )' % (V, Gm, V, TPI, ESUM('j')))], 'eqtr4d',
                                                   '( %s ` j ) = ( %s - ( %s ` j ) )' % (G1, V, Gm))], 'climsubc2', '( %s -> %s ~~> ( %s - %s ) )' % (A, G1, V, EY))
    ac = w.s([nu, sc, ex(Ab), z0, g1c, t([abv, t([g1v], 'fveq2d', '( abs ` ( %s ` j ) ) = ( abs ` ( %s - ( %s x. %s ) ) )' % (G1, V, TPI, ESUM('j')))], 'eqtr4d',
                                         '( %s ` j ) = ( abs ` ( %s ` j ) )' % (Ab, G1))], 'climabs', '( %s -> %s ~~> ( abs ` ( %s - %s ) ) )' % (A, Ab, V, EY))
    # 2. the bound tends to 0
    ef = s([yc, w.s([w.s([], 'eqid', '%s = %s' % (Tm, Tm))], 'efcvg', '( Y e. CC -> seq 0 ( + , %s ) ~~> ( exp ` Y ) )' % Tm)], 'syl', 'seq 0 ( + , %s ) ~~> ( exp ` Y )' % Tm)
    bd = s([ef, w.s([w.s([], 'seqex', 'seq 0 ( + , %s ) e. _V' % Tm), w.s([], 'fvex', '( exp ` Y ) e. _V')], 'breldm', '( seq 0 ( + , %s ) ~~> ( exp ` Y ) -> seq 0 ( + , %s ) e. dom ~~> )' % (Tm, Tm))],
           'syl', 'seq 0 ( + , %s ) e. dom ~~>' % Tm)
    t0 = w.s([nu, z0, ex(Tm), bd, tmc], 'serf0', '( %s -> %s ~~> 0 )' % (A, Tm))
    cl = Closure(w, A, {'Y': ('RR+', yrp)})
    c0r = cl.mem(c0, 'RR')
    bc = w.s([nu, z0, t0, s([c0r], 'recnd', '%s e. CC' % c0), ex(Bd), tmc, t([bdv, t([tmv], 'oveq2d', '( %s x. ( %s ` j ) ) = ( %s x. ( ( Y ^ j ) / ( ! ` j ) ) )' % (c0, Tm, c0))], 'eqtr4d',
                                                                              '( %s ` j ) = ( %s x. ( %s ` j ) )' % (Bd, c0, Tm))], 'climmulc2', '( %s -> %s ~~> ( %s x. 0 ) )' % (A, Bd, c0))
    # 3. the pointwise bound
    tel = t([t([yj, jm], 'jca', '( Y e. RR+ /\\ j e. NN0 )'), w.inst('z6mtel')], 'syl', '%s = ( %s + ( %s x. %s ) )' % (V, VLn('j'), TPI, ESUM('j')))
    vjc = vlnc(w, Aj, yj, jm, 'j')
    dq = t([t([tel], 'oveq1d', '( %s - ( %s x. %s ) ) = ( ( %s + ( %s x. %s ) ) - ( %s x. %s ) )' % (V, TPI, ESUM('j'), VLn('j'), TPI, ESUM('j'), TPI, ESUM('j'))),
            t([vjc, tsj], 'pncand', '( ( %s + ( %s x. %s ) ) - ( %s x. %s ) ) = %s' % (VLn('j'), TPI, ESUM('j'), TPI, ESUM('j'), VLn('j')))], 'eqtrd',
           '( %s - ( %s x. %s ) ) = %s' % (V, TPI, ESUM('j'), VLn('j')))
    JH = '( j + ( 1 / 2 ) )'
    lf = t([t([yj, jm], 'jca', '( Y e. RR+ /\\ j e. NN0 )'), w.inst('z6mleft')], 'syl',
           '( abs ` %s ) <_ ( ( ( 2 x. ( Y ^c %s ) ) / ( ! ` j ) ) x. %s )' % (VLn('j'), JH, KG))
    ycj = t([yj], 'rpcnd', 'Y e. CC'); jc = t([jm], 'nn0cnd', 'j e. CC')
    ca = t([t([ycj, t([yj], 'rpne0d', 'Y =/= 0')], 'jca', '( Y e. CC /\\ Y =/= 0 )'), jc, a1c(w, Aj, 'halfcn', '( 1 / 2 ) e. CC'), w.inst('cxpadd')], 'syl3anc',
           '( Y ^c %s ) = ( ( Y ^c j ) x. ( Y ^c ( 1 / 2 ) ) )' % JH)
    ce = t([ca, t([t([ycj, jm, w.inst('cxpexp')], 'syl2anc', '( Y ^c j ) = ( Y ^ j )')], 'oveq1d', '( ( Y ^c j ) x. ( Y ^c ( 1 / 2 ) ) ) = ( ( Y ^ j ) x. ( Y ^c ( 1 / 2 ) ) )')],
           'eqtrd', '( Y ^c %s ) = ( ( Y ^ j ) x. ( Y ^c ( 1 / 2 ) ) )' % JH)
    YH = '( Y ^c ( 1 / 2 ) )'
    cj = Closure(w, Aj, {'Y': ('RR+', yj)})
    kgc = t([cj.mem(KG, 'RR')], 'recnd', '%s e. CC' % KG)
    al = t([t([t([ycj, jm], 'expcld', '( Y ^ j ) e. CC'), t([cj.mem(YH, 'RR')], 'recnd', '%s e. CC' % YH)], 'jca', '( ( Y ^ j ) e. CC /\\ %s e. CC )' % YH),
            t([t([fnj], 'nncnd', '( ! ` j ) e. CC'), t([fnj], 'nnne0d', '( ! ` j ) =/= 0')], 'jca', '( ( ! ` j ) e. CC /\\ ( ! ` j ) =/= 0 )'), kgc, w.inst('z6malg3')], 'syl3anc',
           '( ( ( 2 x. ( ( Y ^ j ) x. %s ) ) / ( ! ` j ) ) x. %s ) = ( ( ( 2 x. %s ) x. %s ) x. ( ( Y ^ j ) / ( ! ` j ) ) )' % (YH, KG, YH, KG))
    BL = '( ( ( 2 x. ( Y ^c %s ) ) / ( ! ` j ) ) x. %s )' % (JH, KG)
    be = t([t([t([t([ce], 'oveq2d', '( 2 x. ( Y ^c %s ) ) = ( 2 x. ( ( Y ^ j ) x. %s ) )' % (JH, YH))], 'oveq1d',
                 '( ( 2 x. ( Y ^c %s ) ) / ( ! ` j ) ) = ( ( 2 x. ( ( Y ^ j ) x. %s ) ) / ( ! ` j ) )' % (JH, YH))], 'oveq1d',
              '%s = ( ( ( 2 x. ( ( Y ^ j ) x. %s ) ) / ( ! ` j ) ) x. %s )' % (BL, YH, KG)), al], 'eqtrd', '%s = ( %s x. ( ( Y ^ j ) / ( ! ` j ) ) )' % (BL, c0))
    lf2 = t([lf, be], 'breqtrd', '( abs ` %s ) <_ ( %s x. ( ( Y ^ j ) / ( ! ` j ) ) )' % (VLn('j'), c0))
    ad = t([abv, t([dq], 'fveq2d', '( abs ` ( %s - ( %s x. %s ) ) ) = ( abs ` %s )' % (V, TPI, ESUM('j'), VLn('j')))], 'eqtrd', '( %s ` j ) = ( abs ` %s )' % (Ab, VLn('j')))
    pw = t([t([ad, lf2], 'eqbrtrd', '( %s ` j ) <_ ( %s x. ( ( Y ^ j ) / ( ! ` j ) ) )' % (Ab, c0)), bdv], 'breqtrrd', '( %s ` j ) <_ ( %s ` j )' % (Ab, Bd))
    abr = t([ad, t([vjc], 'abscld', '( abs ` %s ) e. RR' % VLn('j'))], 'eqeltrd', '( %s ` j ) e. RR' % Ab)
    tmr = t([t([t([yj], 'rpred', 'Y e. RR'), jm], 'reexpcld', '( Y ^ j ) e. RR'), t([fnj], 'nnrpd', '( ! ` j ) e. RR+')], 'rerpdivcld', '( ( Y ^ j ) / ( ! ` j ) ) e. RR')
    bdr = t([bdv, t([lift(w, c0r, Aj), tmr], 'remulcld', '( %s x. ( ( Y ^ j ) / ( ! ` j ) ) ) e. RR' % c0)], 'eqeltrd', '( %s ` j ) e. RR' % Bd)
    le = w.s([nu, z0, ac, bc, abr, bdr, pw], 'climle', '( %s -> ( abs ` ( %s - %s ) ) <_ ( %s x. 0 ) )' % (A, V, EY, c0))
    le0 = s([le, s([s([c0r], 'recnd', '%s e. CC' % c0)], 'mul01d', '( %s x. 0 ) = 0' % c0)], 'breqtrd', '( abs ` ( %s - %s ) ) <_ 0' % (V, EY))
    dc = s([vc, ec], 'subcld', '( %s - %s ) e. CC' % (V, EY))
    ar = s([dc], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (V, EY))
    a0 = s([s([le0, s([dc], 'absge0d', '0 <_ ( abs ` ( %s - %s ) )' % (V, EY))], 'jca', '( ( abs ` ( %s - %s ) ) <_ 0 /\\ 0 <_ ( abs ` ( %s - %s ) ) )' % (V, EY, V, EY)),
            s([ar, a1c(w, A, '0re', '0 e. RR')], 'letri3d', '( ( abs ` ( %s - %s ) ) = 0 <-> ( ( abs ` ( %s - %s ) ) <_ 0 /\\ 0 <_ ( abs ` ( %s - %s ) ) ) )' % (V, EY, V, EY, V, EY))],
           'mpbird', '( abs ` ( %s - %s ) ) = 0' % (V, EY))
    d0 = s([a0, s([dc, w.inst('abs00')], 'syl', '( ( abs ` ( %s - %s ) ) = 0 <-> ( %s - %s ) = 0 )' % (V, EY, V, EY))], 'mpbid', '( %s - %s ) = 0' % (V, EY))
    w.qed([vc, ec, d0], 'subeq0d', STATEMENTS['z6mhalf'])
    return w


# ---------------------------------------------------------------- z6mellin
def z6mellin():
    w = W('z6mellin', 'The Mellin identity: for ` 1 / 2 <_ C <_ 3 ` the vertical line integrals of ` _G ( w ) Y ^ -u w ` converge to '
          '` 2 pi i e ^ -u Y ` (DetectionShift.lean ` integral_Gamma_cpow_line ` ; ~ z6mvlr , ~ z6mright , ~ z6mhalf ).')
    A = split_imp(STATEMENTS['z6mellin'])[0]
    s = mkst(w, A)
    idA = w.s([], 'id', '( %s -> %s )' % (A, A))
    l = s([idA, w.inst('z6mvlr')], 'syl', '%s ~~>r %s' % (VLF(GYM, 'C'), VL(GYM, 'C')))
    r = s([idA, w.inst('z6mright')], 'syl', '%s = %s' % (VL(GYM, 'C'), VLH))
    h = s([w.s([], 'simpl', '( %s -> Y e. RR+ )' % A), w.inst('z6mhalf')], 'syl', '%s = %s' % (VLH, EY))
    w.qed([l, s([r, h], 'eqtrd', '%s = %s' % (VL(GYM, 'C'), EY))], 'breqtrd', STATEMENTS['z6mellin'])
    return w


# ---------------------------------------------------------------- z6mg32
def z6mg32():
    w = W('z6mg32', 'Gamma on ` Re W = 3 ` : ` | _G ( W ) | <_ 32 2 ^ ( - | Im W | / 4 ) ` ( ~ gamvb , ` _G ( 3 ) = 2 ! = 2 ` by ~ gamfac ).')
    A = split_imp(STATEMENTS['z6mg32'])[0]
    s = mkst(w, A)
    wc = w.s([], 'simpl', '( %s -> W e. CC )' % A); r3 = w.s([], 'simpr', '( %s -> ( Re ` W ) = 3 )' % A)
    gt = s([a1c(w, A, '3pos', '0 < 3'), r3], 'breqtrrd', '0 < ( Re ` W )')
    le = s([r3], 'eqled', '( Re ` W ) <_ 3')
    AI = '( abs ` ( Im ` W ) )'
    e2, e4 = E2(AI), E4(AI)
    gv = s([s([wc, gt, le], '3jca', '( W e. CC /\\ 0 < ( Re ` W ) /\\ ( Re ` W ) <_ 3 )'), w.inst('gamvb')], 'syl',
           '( abs ` ( _G ` W ) ) <_ ( ( ; 1 6 x. ( _G ` ( Re ` W ) ) ) x. %s )' % e2)
    g3 = w.s([w.s([w.s([], '3nn', '3 e. NN'), w.inst('gamfac')], 'ax-mp', '( _G ` 3 ) = ( ! ` ( 3 - 1 ) )'),
              w.s([w.s([w.s([], '3m1e2', '( 3 - 1 ) = 2')], 'fveq2i', '( ! ` ( 3 - 1 ) ) = ( ! ` 2 )'), w.s([], 'fac2', '( ! ` 2 ) = 2')], 'eqtri', '( ! ` ( 3 - 1 ) ) = 2')],
             'eqtri', '( _G ` 3 ) = 2')
    gr = s([s([r3], 'fveq2d', '( _G ` ( Re ` W ) ) = ( _G ` 3 )'), a1(w, A, g3, '( _G ` 3 ) = 2')], 'eqtrd', '( _G ` ( Re ` W ) ) = 2')
    m16 = num.mul_lits(w, '; 1 6', '2')
    c32 = s([s([gr], 'oveq2d', '( ; 1 6 x. ( _G ` ( Re ` W ) ) ) = ( ; 1 6 x. 2 )'), a1(w, A, m16, cnst_closed(w, m16))], 'eqtrd', '( ; 1 6 x. ( _G ` ( Re ` W ) ) ) = ; 3 2')
    gv2 = s([gv, s([c32], 'oveq1d', '( ( ; 1 6 x. ( _G ` ( Re ` W ) ) ) x. %s ) = ( ; 3 2 x. %s )' % (e2, e2))], 'breqtrd', '( abs ` ( _G ` W ) ) <_ ( ; 3 2 x. %s )' % e2)
    air = s([s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')], 'abscld', '%s e. RR' % AI)
    cl = Closure(w, A, {AI: ('RR', air)})
    n2 = cl.mem('-u ( %s / 2 )' % AI, 'RR'); n4 = cl.mem('-u ( %s / 4 )' % AI, 'RR')
    e2r = s([s([cl.mem('2', 'RR+'), n2], 'rpcxpcld', '%s e. RR+' % e2)], 'rpred', '%s e. RR' % e2)
    e4r = s([s([cl.mem('2', 'RR+'), n4], 'rpcxpcld', '%s e. RR+' % e4)], 'rpred', '%s e. RR' % e4)
    aige = s([s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')], 'absge0d', '0 <_ %s' % AI)
    nle = linarith(w, A, [aige], '-u ( %s / 2 ) <_ -u ( %s / 4 )' % (AI, AI), closure=cl)
    e24 = s([s([cl.mem('2', 'RR'), w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % A)], 'jca', '( 2 e. RR /\\ 1 <_ 2 )'),
             s([n2, n4], 'jca', '( -u ( %s / 2 ) e. RR /\\ -u ( %s / 4 ) e. RR )' % (AI, AI)), nle, w.inst('cxplea')], 'syl3anc', '%s <_ %s' % (e2, e4))
    r32 = cl.mem('; 3 2', 'RR')
    m2 = s([e2r, e4r, r32, cl.ge0('; 3 2'), e24], 'lemul2ad', '( ; 3 2 x. %s ) <_ ( ; 3 2 x. %s )' % (e2, e4))
    gdr = s([gv2, w.inst('z6absle')], 'syl', '( _G ` W ) e. CC')
    w.qed([s([gdr], 'abscld', '( abs ` ( _G ` W ) ) e. RR'), s([r32, e2r], 'remulcld', '( ; 3 2 x. %s ) e. RR' % e2), s([r32, e4r], 'remulcld', '( ; 3 2 x. %s ) e. RR' % e4), gv2, m2],
          'letrd', STATEMENTS['z6mg32'])
    return w


def cnst_closed(w, step):
    for l in w.lines:
        if l.startswith(step + ':'):
            return l.split('|-', 1)[1].strip()
    raise KeyError(step)


# ---------------------------------------------------------------- z6mtail
def z6mtail():
    w = W('z6mtail', 'The quantitative Mellin identity on ` Re w = 3 ` : ` | LI ( 3 , T ) - 2 pi i e ^ -u Y | <_ Y ^ -u 3 ( 256 / log 2 ) 2 ^ ( - T / 4 ) ` '
          '(the tail ~ z6vlt at ` M = 32 Y ^ -u 3 ` , ~ z6mg32 ; the value by ~ z6mright and ~ z6mhalf ).')
    A = split_imp(STATEMENTS['z6mtail'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A); trp = w.s([], 'simpr', '( %s -> T e. RR+ )' % A)
    Y3 = '( Y ^c -u 3 )'
    M = '( ; 3 2 x. %s )' % Y3
    Au = '( %s /\\ u e. RR )' % A
    t = mkst(w, Au)
    vr = w.s([], 'simpr', '( %s -> u e. RR )' % Au)
    Z = '( 3 + ( _i x. u ) )'
    r3 = a1c(w, Au, '3re', '3 e. RR')
    zc = t([a1c(w, Au, '3cn', '3 e. CC'), t([a1c(w, Au, 'ax-icn', '_i e. CC'), t([vr], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % Z)
    re = t([r3, vr], 'crred', '( Re ` %s ) = 3' % Z); im = t([r3, vr], 'crimd', '( Im ` %s ) = u' % Z)
    zdg = t([zc, t([a1c(w, Au, '3pos', '0 < 3'), re], 'breqtrrd', '0 < ( Re ` %s )' % Z), w.inst('zrenn')], 'syl2anc', '%s e. %s' % (Z, DG))
    ald = s([zdg], 'ralrimiva', 'A. u e. RR %s e. %s' % (Z, DG))
    g32 = t([zc, re, w.inst('z6mg32')], 'syl2anc', '( abs ` ( _G ` %s ) ) <_ ( ; 3 2 x. %s )' % (Z, E4('( abs ` ( Im ` %s ) )' % Z)))
    aim = t([im], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % Z)
    a = t([aim], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % Z)
    b = t([a], 'negeqd', '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % Z)
    c = t([b], 'oveq2d', '%s = %s' % (E4('( abs ` ( Im ` %s ) )' % Z), E4('( abs ` u )')))
    EV = E4('( abs ` u )')
    g32b = t([g32, t([c], 'oveq2d', '( ; 3 2 x. %s ) = ( ; 3 2 x. %s )' % (E4('( abs ` ( Im ` %s ) )' % Z), EV))], 'breqtrd', '( abs ` ( _G ` %s ) ) <_ ( ; 3 2 x. %s )' % (Z, EV))
    yv = t([lift(w, yrp, Au)], 'rpcnd', 'Y e. CC')
    nz = t([zc], 'negcld', '-u %s e. CC' % Z)
    ay = t([t([lift(w, yrp, Au), nz, w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c -u %s ) ) = ( Y ^c ( Re ` -u %s ) )' % (Z, Z)),
            t([t([t([zc], 'renegd', '( Re ` -u %s ) = -u ( Re ` %s )' % (Z, Z)), t([re], 'negeqd', '-u ( Re ` %s ) = -u 3' % Z)], 'eqtrd', '( Re ` -u %s ) = -u 3' % Z)], 'oveq2d',
              '( Y ^c ( Re ` -u %s ) ) = %s' % (Z, Y3))], 'eqtrd', '( abs ` ( Y ^c -u %s ) ) = %s' % (Z, Y3))
    gc = t([g32b, w.inst('z6absle')], 'syl', '( _G ` %s ) e. CC' % Z)
    yzc = t([yv, nz], 'cxpcld', '( Y ^c -u %s ) e. CC' % Z)
    am = t([t([gc, yzc], 'absmuld', '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) = ( ( abs ` ( _G ` %s ) ) x. ( abs ` ( Y ^c -u %s ) ) )' % (Z, Z, Z, Z)),
            t([ay], 'oveq2d', '( ( abs ` ( _G ` %s ) ) x. ( abs ` ( Y ^c -u %s ) ) ) = ( ( abs ` ( _G ` %s ) ) x. %s )' % (Z, Z, Z, Y3))], 'eqtrd',
           '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) = ( ( abs ` ( _G ` %s ) ) x. %s )' % (Z, Z, Z, Y3))
    cv = Closure(w, Au, {'Y': ('RR+', lift(w, yrp, Au)), 'u': ('RR', vr)})
    y3p = t([lift(w, yrp, Au), cv.mem('-u 3', 'RR')], 'rpcxpcld', '%s e. RR+' % Y3)
    E32 = '( ; 3 2 x. %s )' % EV
    m = t([t([gc], 'abscld', '( abs ` ( _G ` %s ) ) e. RR' % Z), cv.mem(E32, 'RR'), t([y3p], 'rpred', '%s e. RR' % Y3), t([y3p], 'rpge0d', '0 <_ %s' % Y3), g32b], 'lemul1ad',
          '( ( abs ` ( _G ` %s ) ) x. %s ) <_ ( %s x. %s )' % (Z, Y3, E32, Y3))
    r = t([t([cv.mem('; 3 2', 'RR')], 'recnd', '; 3 2 e. CC'), t([cv.mem(EV, 'RR')], 'recnd', '%s e. CC' % EV), t([y3p], 'rpcnd', '%s e. CC' % Y3)], 'mul32d',
          '( %s x. %s ) = ( %s x. %s )' % (E32, Y3, M, EV))
    bb = t([t([am, m], 'eqbrtrd', '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s )' % (Z, Z, E32, Y3)), r], 'breqtrd',
           '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s )' % (Z, Z, M, EV))
    gv, _ = mpval(w, Au, 'w', DG, '( ( _G ` w ) x. ( Y ^c -u w ) )', Z, zdg)
    bg = t([t([gv], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) )' % (GYM, Z, Z, Z)), bb], 'eqbrtrd',
           '( abs ` ( %s ` %s ) ) <_ ( %s x. %s )' % (GYM, Z, M, EV))
    BV = '( T <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) )' % (GYM, Z, M, EV)
    alb = s([w.s([bg], 'a1d', '( %s -> %s )' % (Au, BV))], 'ralrimiva', 'A. u e. RR %s' % BV)
    cl = Closure(w, A, {'Y': ('RR+', yrp), 'T': ('RR+', trp)})
    gyh = s([yrp, w.inst('z6gyhol')], 'syl', HOLG(GYM, DG))
    gyc = s([gyh], 'simpld', '%s e. ( %s -cn-> CC )' % (GYM, DG))
    HV = sub(split_imp(STATEMENTS['z6vlcvg'])[0], {'C': '3', 'G': GYM, 'D': DG, 'M': M, 'Y': 'T'})
    h = s([s([a1c(w, A, '3re', '3 e. RR'), s([gyc, ald], 'jca', '( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s )' % (GYM, DG, Z, DG))], 'jca',
             '( 3 e. RR /\\ ( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s ) )' % (GYM, DG, Z, DG)),
           s([s([cl.mem(M, 'RR'), trp], 'jca', '( %s e. RR /\\ T e. RR+ )' % M), alb], 'jca', '( ( %s e. RR /\\ T e. RR+ ) /\\ A. u e. RR %s )' % (M, BV))], 'jca', HV)
    V3 = VL(GYM, '3')
    LT = LI(GYM, '3', 'T')
    tr = s([trp], 'rpred', 'T e. RR')
    B1 = '( ( ( 8 x. %s ) / ( log ` 2 ) ) x. %s )' % (M, E4('T'))
    tb = s([h, s([trp, s([tr], 'leidd', 'T <_ T')], 'jca', '( T e. RR+ /\\ T <_ T )'), w.inst('z6vlt')], 'syl2anc', '( abs ` ( %s - %s ) ) <_ %s' % (V3, LT, B1))
    # the value
    A3 = '( Y e. RR+ /\\ ( 3 e. RR /\\ ( ( 1 / 2 ) <_ 3 /\\ 3 <_ 3 ) ) )'
    h3 = s([yrp, s([a1c(w, A, '3re', '3 e. RR'), s([w.s([num.le_lit(w, H, '3')], 'a1i', '( %s -> %s <_ 3 )' % (A, H)), s([a1c(w, A, '3re', '3 e. RR')], 'leidd', '3 <_ 3')], 'jca',
                                                                            '( ( 1 / 2 ) <_ 3 /\\ 3 <_ 3 )')], 'jca', '( 3 e. RR /\\ ( ( 1 / 2 ) <_ 3 /\\ 3 <_ 3 ) )')], 'jca', A3)
    v3 = s([s([h3, w.inst('z6mright')], 'syl', '%s = %s' % (V3, VLH)), s([yrp, w.inst('z6mhalf')], 'syl', '%s = %s' % (VLH, EY))], 'eqtrd', '%s = %s' % (V3, EY))
    ltc = s([s([h3, w.inst('z6mvlr')], 'syl', '%s ~~>r %s' % (VLF(GYM, '3'), V3)), w.inst('rlimcl')], 'syl', '%s e. CC' % V3)
    SA = '( 3 + ( _i x. -u T ) )'; SB = '( 3 + ( _i x. T ) )'
    seg = s([s([s([a1c(w, A, '3re', '3 e. RR'), trp], 'jca', '( 3 e. RR /\\ T e. RR+ )'), ald], 'jca', '( ( 3 e. RR /\\ T e. RR+ ) /\\ A. u e. RR %s e. %s )' % (Z, DG)),
             w.inst('z6segd')], 'syl', '( %s cseg %s ) C_ %s' % (SA, SB, DG))
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    sac = s([a1c(w, A, '3cn', '3 e. CC'), s([ic, s([s([tr], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % SA)
    sbc = s([a1c(w, A, '3cn', '3 e. CC'), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SB)
    lcc = s([s([sac, sbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), s([gyc, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (GYM, DG, SA, SB, DG)),
             w.inst('lintcl')], 'syl2anc', '%s e. CC' % LT)
    ab1 = s([s([v3], 'oveq2d', '( %s - %s ) = ( %s - %s )' % (LT, V3, LT, EY))], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (LT, V3, LT, EY))
    ab2 = s([lcc, ltc], 'abssubd', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (LT, V3, V3, LT))
    ab3 = s([ab1, ab2], 'eqtr3d', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (LT, EY, V3, LT))
    tb2 = s([ab3, tb], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ %s' % (LT, EY, B1))
    # the constant
    y3c = s([s([yrp, cl.mem('-u 3', 'RR')], 'rpcxpcld', '%s e. RR+' % Y3)], 'rpcnd', '%s e. CC' % Y3)
    L2 = '( log ` 2 )'
    l2p = cl.mem(L2, 'RR+')
    l2c = s([l2p], 'rpcnd', '%s e. CC' % L2); l2n = s([l2p], 'rpne0d', '%s =/= 0' % L2)
    m8 = num.mul_lits(w, '8', '; 3 2')
    c8 = a1c(w, A, '8cn', '8 e. CC'); c32 = s([cl.mem('; 3 2', 'RR')], 'recnd', '; 3 2 e. CC')
    k1 = s([s([s([c8, c32, y3c], 'mulassd', '( ( 8 x. ; 3 2 ) x. %s ) = ( 8 x. %s )' % (Y3, M))], 'eqcomd', '( 8 x. %s ) = ( ( 8 x. ; 3 2 ) x. %s )' % (M, Y3)),
            s([a1(w, A, m8, cnst_closed(w, m8))], 'oveq1d', '( ( 8 x. ; 3 2 ) x. %s ) = ( ; ; 2 5 6 x. %s )' % (Y3, Y3))], 'eqtrd', '( 8 x. %s ) = ( ; ; 2 5 6 x. %s )' % (M, Y3))
    c256 = s([cl.mem('; ; 2 5 6', 'RR')], 'recnd', '; ; 2 5 6 e. CC')
    k2 = s([s([k1], 'oveq1d', '( ( 8 x. %s ) / %s ) = ( ( ; ; 2 5 6 x. %s ) / %s )' % (M, L2, Y3, L2)),
            s([s([c256, y3c], 'mulcomd', '( ; ; 2 5 6 x. %s ) = ( %s x. ; ; 2 5 6 )' % (Y3, Y3))], 'oveq1d', '( ( ; ; 2 5 6 x. %s ) / %s ) = ( ( %s x. ; ; 2 5 6 ) / %s )' % (Y3, L2, Y3, L2))],
           'eqtrd', '( ( 8 x. %s ) / %s ) = ( ( %s x. ; ; 2 5 6 ) / %s )' % (M, L2, Y3, L2))
    k3 = s([k2, s([y3c, c256, l2c, l2n], 'divassd', '( ( %s x. ; ; 2 5 6 ) / %s ) = ( %s x. ( ; ; 2 5 6 / %s ) )' % (Y3, L2, Y3, L2))], 'eqtrd',
           '( ( 8 x. %s ) / %s ) = ( %s x. ( ; ; 2 5 6 / %s ) )' % (M, L2, Y3, L2))
    e4c = s([s([cl.mem('2', 'RR+'), cl.mem('-u ( T / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % E4('T'))], 'rpcnd', '%s e. CC' % E4('T'))
    k4 = s([s([k3], 'oveq1d', '%s = ( ( %s x. ( ; ; 2 5 6 / %s ) ) x. %s )' % (B1, Y3, L2, E4('T'))),
            s([y3c, s([c256, l2c, l2n], 'divcld', '( ; ; 2 5 6 / %s ) e. CC' % L2), e4c], 'mulassd',
              '( ( %s x. ( ; ; 2 5 6 / %s ) ) x. %s ) = ( %s x. ( ( ; ; 2 5 6 / %s ) x. %s ) )' % (Y3, L2, E4('T'), Y3, L2, E4('T')))], 'eqtrd',
           '%s = ( %s x. ( ( ; ; 2 5 6 / %s ) x. %s ) )' % (B1, Y3, L2, E4('T')))
    fin = s([tb2, k4], 'breqtrd', STATEMENTS['z6mtail'].split(' -> ', 1)[1][:-2])
    toqed(w, fin, 'z6mtail')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6mtel, z6malg3, z6mhalf, z6mellin, z6mg32, z6mtail]:
        if want(f.__name__):
            if run(f()):
                status(f.__name__)
            else:
                break
