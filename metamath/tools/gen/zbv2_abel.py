"""Sortie ZBV2, section 1 part C: the generic second-order Abel summation, with
function variables A (coefficients), G (kernel), R, L (chord slopes and gaps,
G(i) - G(i+1) = R(i) L(i)), F (second-order partial sums, F(i+1) - F(i) =
L(i) sum_{n<=i} A(n)), P (a floor for R(N)), M (a bound for |F|).

bvabellem1  sum_ n <= N A(n) ( G(n) - G(N+1) ) = sum_ i <= N ( G(i) - G(i+1) ) sum_{n<=i} A(n)   [fsumparts]
bvabellem2  sum_ i <= N R(i) ( F(i+1) - F(i) ) = sum_{i<N} ( R(i) - R(i+1) ) F(i+1) + ( R(N) F(N+1) - R(1) F(1) )  [fsumm1, fsumparts]
bvabellem3  sum_ n <= N A(n) ( G(n) - G(N+1) ) - P F(N+1) = sum_{i<N} ( R(i) - R(i+1) ) F(i+1) + ( R(N) - P ) F(N+1)
bvabelin    | the same | <= M ( R(1) - P )   [fsumabs, fsumle, telfsumo]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *

PH = 'ph'
N1 = '( N + 1 )'
FZN, FZN1, FZO = '( 1 ... N )', '( 1 ... ( N + 1 ) )', '( 1 ..^ N )'


def nfacts(w, h1):
    """N e. NN (step h1): ZZ, RR, CC, N e. ( ZZ>= ` 1 ), ( N + 1 ) e. ( ZZ>= ` 1 )"""
    st = mkst(w, PH)
    nz = st([h1], 'nnzd', 'N e. ZZ'); nre = st([h1], 'nnred', 'N e. RR'); ncc = st([h1], 'nncnd', 'N e. CC')
    uz = st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)
    nuz = st([h1, uz], 'eleqtrd', 'N e. ( ZZ>= ` 1 )')
    n1uz = st([st([h1], 'peano2nnd', '%s e. NN' % N1), uz], 'eleqtrd', '%s e. ( ZZ>= ` 1 )' % N1)
    return nz, nre, ncc, nuz, n1uz


def subh(w, A, V, Tk):
    """the fsumparts substitution hypothesis ( k = Tk -> ( A = A' /\\ V = V' ) ); returns (step, A', V')"""
    eq = 'k = %s' % Tk
    idk = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    s1, a1 = w.congr(A, {'k': Tk}, eq, {'k': idk})
    s2, v1 = w.congr(V, {'k': Tk}, eq, {'k': idk})
    return w.s([s1, s2], 'jca', '( %s -> ( %s = %s /\\ %s = %s ) )' % (eq, A, a1, V, v1)), a1, v1


def val_at(w, ante1, hstep, rng, T, body, mem, var='i'):
    """hstep: ( ( ph /\\ var e. rng ) -> body ); mem: ( ante1 -> T e. rng ): ( ante1 -> body[T/var] )
    through the dummy k (T may contain the caller's letters)"""
    rk, bodyk = rename(w, PH, rng, var, 'k', hstep, body)
    return instl(w, PH, ante1, rng, 'k', T, rk, bodyk, mem)


def asa_cl(w, ante, phst, h2, T, nuzT, kind='CC'):
    """( ante -> sum_ n e. ( 1 ... T ) ( A ` n ) e. kind ) from nuzT: ( ante -> N e. ( ZZ>= ` T ) )
    and h2: ( ( ph /\\ n e. ( 1 ... N ) ) -> ( A ` n ) e. kind )"""
    st = mkst(w, ante)
    ss = sy(w, ante, nuzT, 'fzss2', '( 1 ... %s ) C_ %s' % (T, FZN))
    AN = '( %s /\\ n e. ( 1 ... %s ) )' % (ante, T)
    sn = mkst(w, AN)
    nel = sn([lift(w, ss, AN), sn([], 'simpr', 'n e. ( 1 ... %s )' % T)], 'sseldd', 'n e. %s' % FZN)
    anc = hyp2(w, AN, lift(w, phst, AN), nel, h2, '%s e. %s' % (FA('n'), kind))
    return st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % T), anc], 'fsumrecl' if kind == 'RR' else 'fsumcl', '%s e. %s' % (ASA(T), kind))


def bvabellem1():
    w = W('bvabellem1', 'The triangular swap of a second-order Abel sum: sum_ n <= N A ( n ) ( G ( n ) - G ( N + 1 ) ) '
                        '= sum_ i <= N ( G ( i ) - G ( i + 1 ) ) sum_ n <= i A ( n ), by summation by parts against '
                        'the partial sums of A (fsumparts).')
    h1, h2, h3 = hyps_of(w, 'bvabellem1')
    st = mkst(w, PH)
    nz, nre, ncc, nuz, n1uz = nfacts(w, h1)
    Ak = '( %s - %s )' % (FG('k'), FG(N1)); Vk = 'sum_ n e. ( 1 ... ( k - 1 ) ) %s' % FA('n')
    hb, B, Wj = subh(w, Ak, Vk, 'i'); hc, Cc, X = subh(w, Ak, Vk, '( i + 1 )'); hd, D, Y = subh(w, Ak, Vk, '1'); he, Ee, Z = subh(w, Ak, Vk, N1)
    # closures on ( 1 ... ( N + 1 ) ) for the sequence variable k
    AK = '( ph /\\ k e. %s )' % FZN1
    sk = mkst(w, AK)
    kel = sk([], 'simpr', 'k e. %s' % FZN1)
    gk, _ = rename(w, PH, FZN1, 'i', 'k', h3, '%s e. CC' % FG('i'))
    memN1 = sy(w, PH, n1uz, 'eluzfz2', '%s e. %s' % (N1, FZN1))
    gN1, _ = inst(w, PH, FZN1, 'i', N1, h3, '%s e. CC' % FG('i'), memN1)
    akc = sk([gk, lift(w, gN1, AK)], 'subcld', '%s e. CC' % Ak)
    kz = sy(w, AK, kel, 'elfzelz', 'k e. ZZ'); km1z = sy(w, AK, kz, 'peano2zm', '( k - 1 ) e. ZZ')
    kle = sy(w, AK, kel, 'elfzle2', 'k <_ %s' % N1)
    km1le = linarith(w, AK, [kle], '( k - 1 ) <_ N', leaves={'k': sk([kz], 'zred', 'k e. RR'), 'N': lift(w, nre, AK)})
    uzb = sy2(w, AK, km1z, lift(w, nz, AK), 'eluz', '( N e. ( ZZ>= ` ( k - 1 ) ) <-> ( k - 1 ) <_ N )')
    nuzk = sk([km1le, uzb], 'mpbird', 'N e. ( ZZ>= ` ( k - 1 ) )')
    vkc = asa_cl(w, AK, sk([], 'simpl', 'ph'), h2, '( k - 1 )', nuzk)
    S1o = 'sum_ i e. ( 1 ..^ %s ) ( %s x. ( %s - %s ) )' % (N1, B, X, Wj)
    S2o = 'sum_ i e. ( 1 ..^ %s ) ( ( %s - %s ) x. %s )' % (N1, Cc, B, X)
    parts = st([hb, hc, hd, he, n1uz, akc, vkc], 'fsumparts', '%s = ( ( ( %s x. %s ) - ( %s x. %s ) ) - %s )' % (S1o, Ee, Z, D, Y, S2o))
    fz3 = sy(w, PH, nz, 'fzval3', '%s = ( 1 ..^ %s )' % (FZN, N1))
    S1 = 'sum_ i e. %s ( %s x. ( %s - %s ) )' % (FZN, B, X, Wj); S2 = 'sum_ i e. %s ( ( %s - %s ) x. %s )' % (FZN, Cc, B, X)
    r1 = st([fz3], 'sumeq1d', '%s = %s' % (S1, S1o)); r2 = st([fz3], 'sumeq1d', '%s = %s' % (S2, S2o))
    # under i e. ( 1 ... N )
    AI = '( ph /\\ i e. %s )' % FZN
    si = mkst(w, AI)
    iel = si([], 'simpr', 'i e. %s' % FZN)
    inn = sy(w, AI, iel, 'elfznn', 'i e. NN')
    iuz = si([inn, si([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', 'i e. ( ZZ>= ` 1 )')
    icc = si([inn], 'nncnd', 'i e. CC'); ire = si([inn], 'nnred', 'i e. RR'); iz = si([inn], 'nnzd', 'i e. ZZ')
    phi = si([], 'simpl', 'ph')
    nuzi = sy(w, AI, iel, 'elfzuz3', 'N e. ( ZZ>= ` i )')
    ile = sy(w, AI, iel, 'elfzle2', 'i <_ N')
    im1le = linarith(w, AI, [ile], '( i - 1 ) <_ N', leaves={'i': ire, 'N': lift(w, nre, AI)})
    nuzim1 = si([im1le, sy2(w, AI, sy(w, AI, iz, 'peano2zm', '( i - 1 ) e. ZZ'), lift(w, nz, AI), 'eluz', '( N e. ( ZZ>= ` ( i - 1 ) ) <-> ( i - 1 ) <_ N )')], 'mpbird', 'N e. ( ZZ>= ` ( i - 1 ) )')
    wjc = asa_cl(w, AI, phi, h2, '( i - 1 )', nuzim1)
    asic = asa_cl(w, AI, phi, h2, 'i', nuzi)
    aic, _ = rename(w, PH, FZN, 'n', 'i', h2, '%s e. CC' % FA('n'))
    # X = ASA(i) and X - Wj = ( A ` i )
    pc = si([icc, si([], '1cnd', '1 e. CC')], 'pncand', '( ( i + 1 ) - 1 ) = i')
    xeq = si([si([pc], 'oveq2d', '( 1 ... ( ( i + 1 ) - 1 ) ) = ( 1 ... i )')], 'sumeq1d', '%s = %s' % (X, ASA('i')))
    ss_i = sy(w, AI, nuzi, 'fzss2', '( 1 ... i ) C_ %s' % FZN)
    AIN = '( %s /\\ n e. ( 1 ... i ) )' % AI
    sin = mkst(w, AIN)
    bodyc = hyp2(w, AIN, lift(w, phi, AIN), sin([lift(w, ss_i, AIN), sin([], 'simpr', 'n e. ( 1 ... i )')], 'sseldd', 'n e. %s' % FZN), h2, '%s e. CC' % FA('n'))
    subm = w.s([], 'fveq2', '( n = i -> %s = %s )' % (FA('n'), FA('i')))
    m1 = si([iuz, bodyc, subm], 'fsumm1', '%s = ( %s + %s )' % (ASA('i'), Wj, FA('i')))
    xw = si([si([si([xeq, m1], 'eqtrd', '%s = ( %s + %s )' % (X, Wj, FA('i')))], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (X, Wj, Wj, FA('i'), Wj)),
             si([wjc, aic], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (Wj, FA('i'), Wj, FA('i')))], 'eqtrd', '( %s - %s ) = %s' % (X, Wj, FA('i')))
    # G values under AI
    iel1 = si([si([clo(w, 'fzssp1', '%s C_ %s' % (FZN, FZN1))], 'a1i', '%s C_ %s' % (FZN, FZN1)), iel], 'sseldd', 'i e. %s' % FZN1)
    gic = hyp2(w, AI, phi, iel1, h3, '%s e. CC' % FG('i'))
    gi1c, _ = val_at(w, AI, h3, FZN1, '( i + 1 )', '%s e. CC' % FG('i'), sy(w, AI, iel, 'fzp1elp1', '( i + 1 ) e. %s' % FZN1))
    gn1i = lift(w, gN1, AI)
    bc = si([gic, gn1i], 'subcld', '%s e. CC' % B)
    body1 = si([si([xw], 'oveq2d', '( %s x. ( %s - %s ) ) = ( %s x. %s )' % (B, X, Wj, B, FA('i'))), si([bc, aic], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (B, FA('i'), FA('i'), B))], 'eqtrd',
               '( %s x. ( %s - %s ) ) = ( %s x. %s )' % (B, X, Wj, FA('i'), B))
    DG = '( %s - %s )' % (FG('i'), FG('( i + 1 )'))
    BODYSW = '( %s x. %s )' % (DG, ASA('i'))
    cb = si([gi1c, gic, gn1i], 'nnncan2d', '( %s - %s ) = ( %s - %s )' % (Cc, B, FG('( i + 1 )'), FG('i')))
    cb2 = si([cb, si([si([gic, gi1c], 'negsubdi2d', '-u %s = ( %s - %s )' % (DG, FG('( i + 1 )'), FG('i')))], 'eqcomd', '( %s - %s ) = -u %s' % (FG('( i + 1 )'), FG('i'), DG))], 'eqtrd',
              '( %s - %s ) = -u %s' % (Cc, B, DG))
    dgc = si([gic, gi1c], 'subcld', '%s e. CC' % DG)
    body2 = si([si([cb2, xeq], 'oveq12d', '( ( %s - %s ) x. %s ) = ( -u %s x. %s )' % (Cc, B, X, DG, ASA('i'))), si([dgc, asic], 'mulneg1d', '( -u %s x. %s ) = -u %s' % (DG, ASA('i'), BODYSW))], 'eqtrd',
               '( ( %s - %s ) x. %s ) = -u %s' % (Cc, B, X, BODYSW))
    bswc = si([dgc, asic], 'mulcld', '%s e. CC' % BODYSW)
    fin = st([], 'fzfid', '%s e. Fin' % FZN)
    SM = 'sum_ i e. %s ( %s x. %s )' % (FZN, FA('i'), B)
    e1 = st([body1], 'sumeq2dv', '%s = %s' % (S1, SM))
    idin = w.s([], 'id', '( i = n -> i = n )')
    cbst, cbnew = w.congr('( %s x. %s )' % (FA('i'), B), {'i': 'n'}, 'i = n', {'i': idin})
    assert cbnew == '( %s x. ( %s - %s ) )' % (FA('n'), FG('n'), FG(N1)), cbnew
    cbv = w.s([cbst], 'cbvsumv', '%s = %s' % (SM, SABEL))
    e2 = st([body2], 'sumeq2dv', '%s = sum_ i e. %s -u %s' % (S2, FZN, BODYSW))
    e3 = st([fin, bswc], 'fsumneg', 'sum_ i e. %s -u %s = -u %s' % (FZN, BODYSW, SSWAP))
    s2eq = eqtr(w, PH, [st([r2], 'eqcomd', '%s = %s' % (S2o, S2)), e2, e3], None)
    # E x. Z = 0, D x. Y = 0
    ez = st([gN1], 'subidd', '%s = 0' % Ee)
    nuzN = st([st([ncc, st([], '1cnd', '1 e. CC')], 'pncand', '( %s - 1 ) = N' % N1)], 'fveq2d', '( ZZ>= ` ( %s - 1 ) ) = ( ZZ>= ` N )' % N1)
    nuzZ = st([sy(w, PH, nz, 'uzid', 'N e. ( ZZ>= ` N )'), nuzN], 'eleqtrrd', 'N e. ( ZZ>= ` ( %s - 1 ) )' % N1)
    zc = asa_cl(w, PH, st([], 'id', 'ph'), h2, '( %s - 1 )' % N1, nuzZ)
    ez0 = st([st([ez], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (Ee, Z, Z)), st([zc], 'mul02d', '( 0 x. %s ) = 0' % Z)], 'eqtrd', '( %s x. %s ) = 0' % (Ee, Z))
    y1 = st([st([clo(w, '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( 1 - 1 ) = 0')], 'oveq2d', '( 1 ... ( 1 - 1 ) ) = ( 1 ... 0 )')
    y2 = st([y1, st([clo(w, 'fz10', '( 1 ... 0 ) = (/)')], 'a1i', '( 1 ... 0 ) = (/)')], 'eqtrd', '( 1 ... ( 1 - 1 ) ) = (/)')
    y0 = st([st([y2], 'sumeq1d', '%s = sum_ n e. (/) %s' % (Y, FA('n'))), st([clo(w, 'sum0', 'sum_ n e. (/) %s = 0' % FA('n'))], 'a1i', 'sum_ n e. (/) %s = 0' % FA('n'))], 'eqtrd', '%s = 0' % Y)
    g1c, _ = inst(w, PH, FZN1, 'i', '1', h3, '%s e. CC' % FG('i'), sy(w, PH, n1uz, 'eluzfz1', '1 e. %s' % FZN1))
    dc = st([g1c, gN1], 'subcld', '%s e. CC' % D)
    dy0 = st([st([y0], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (D, Y, D)), st([dc], 'mul01d', '( %s x. 0 ) = 0' % D)], 'eqtrd', '( %s x. %s ) = 0' % (D, Y))
    swc = st([fin, bswc], 'fsumcl', '%s e. CC' % SSWAP)
    rhs = eqtr(w, PH, [st([st([ez0, dy0], 'oveq12d', '( ( %s x. %s ) - ( %s x. %s ) ) = ( 0 - 0 )' % (Ee, Z, D, Y)), s2eq], 'oveq12d',
                          '( ( ( %s x. %s ) - ( %s x. %s ) ) - %s ) = ( ( 0 - 0 ) - -u %s )' % (Ee, Z, D, Y, S2o, SSWAP)),
                       st([st([clo(w, '0m0e0', '( 0 - 0 ) = 0')], 'a1i', '( 0 - 0 ) = 0')], 'oveq1d', '( ( 0 - 0 ) - -u %s ) = ( 0 - -u %s )' % (SSWAP, SSWAP)),
                       st([st([], '0cnd', '0 e. CC'), swc], 'subnegd', '( 0 - -u %s ) = ( 0 + %s )' % (SSWAP, SSWAP)),
                       st([swc], 'addlidd', '( 0 + %s ) = %s' % (SSWAP, SSWAP))], None)
    lhs = eqtr(w, PH, [st([st([cbv], 'a1i', '%s = %s' % (SM, SABEL))], 'eqcomd', '%s = %s' % (SABEL, SM)), st([e1], 'eqcomd', '%s = %s' % (SM, S1)), r1, parts], None)
    w.qed([lhs, rhs], 'eqtrd', '( ph -> %s = %s )' % (SABEL, SSWAP))
    return w


def rf_closures(w, h2, h3, nuz, n1uz):
    """values R(N), F(N), F(N+1), R(1), F(1) in CC under ph (h2 on ( 1 ... N ), h3 on ( 1 ... ( N + 1 ) ))"""
    memN = sy(w, PH, nuz, 'eluzfz2', 'N e. %s' % FZN)
    memN1 = sy(w, PH, n1uz, 'eluzfz2', '%s e. %s' % (N1, FZN1))
    mem1 = sy(w, PH, nuz, 'eluzfz1', '1 e. %s' % FZN)
    st = mkst(w, PH)
    ssp = st([clo(w, 'fzssp1', '%s C_ %s' % (FZN, FZN1))], 'a1i', '%s C_ %s' % (FZN, FZN1))
    memN_1 = st([ssp, memN], 'sseldd', 'N e. %s' % FZN1); mem1_1 = st([ssp, mem1], 'sseldd', '1 e. %s' % FZN1)
    rN, _ = inst(w, PH, FZN, 'i', 'N', h2, '%s e. CC' % FR('i'), memN)
    fN, _ = inst(w, PH, FZN1, 'i', 'N', h3, '%s e. CC' % FF('i'), memN_1)
    fN1, _ = inst(w, PH, FZN1, 'i', N1, h3, '%s e. CC' % FF('i'), memN1)
    r1, _ = inst(w, PH, FZN, 'i', '1', h2, '%s e. CC' % FR('i'), mem1)
    f1, _ = inst(w, PH, FZN1, 'i', '1', h3, '%s e. CC' % FF('i'), mem1_1)
    return rN, fN, fN1, r1, f1


def io_closures(w, h2, h3, kind='CC'):
    """under AIo = ( ph /\\ i e. ( 1 ..^ N ) ): R(i), R(i+1), F(i+1) e. kind; returns (AIo, si, dict)"""
    AIo = '( ph /\\ i e. %s )' % FZO
    si = mkst(w, AIo)
    iel = si([], 'simpr', 'i e. %s' % FZO)
    phi = si([], 'simpl', 'ph')
    ifz = sy(w, AIo, iel, 'elfzofz', 'i e. %s' % FZN)
    ip1 = sy(w, AIo, iel, 'fzofzp1', '( i + 1 ) e. %s' % FZN)
    ip11 = si([si([clo(w, 'fzssp1', '%s C_ %s' % (FZN, FZN1))], 'a1i', '%s C_ %s' % (FZN, FZN1)), ip1], 'sseldd', '( i + 1 ) e. %s' % FZN1)
    ri = hyp2(w, AIo, phi, ifz, h2, '%s e. %s' % (FR('i'), kind))
    ri1, _ = val_at(w, AIo, h2, FZN, '( i + 1 )', '%s e. %s' % (FR('i'), kind), ip1)
    fi1, _ = val_at(w, AIo, h3, FZN1, '( i + 1 )', '%s e. %s' % (FF('i'), kind), ip11)
    return AIo, si, dict(iel=iel, phi=phi, ifz=ifz, ip1=ip1, ip11=ip11, ri=ri, ri1=ri1, fi1=fi1)


def bvabellem2():
    w = W('bvabellem2', 'Summation by parts for sum_ i <= N R ( i ) ( F ( i + 1 ) - F ( i ) ): the term i = N is peeled '
                        '(fsumm1) and fsumparts runs on ( 1 ..^ N ).')
    h1, h2, h3 = hyps_of(w, 'bvabellem2')
    st = mkst(w, PH)
    nz, nre, ncc, nuz, n1uz = nfacts(w, h1)
    AI = '( ph /\\ i e. %s )' % FZN
    si = mkst(w, AI)
    iel = si([], 'simpr', 'i e. %s' % FZN); phi = si([], 'simpl', 'ph')
    iel1 = si([si([clo(w, 'fzssp1', '%s C_ %s' % (FZN, FZN1))], 'a1i', '%s C_ %s' % (FZN, FZN1)), iel], 'sseldd', 'i e. %s' % FZN1)
    fic = hyp2(w, AI, phi, iel1, h3, '%s e. CC' % FF('i'))
    fi1c, _ = val_at(w, AI, h3, FZN1, '( i + 1 )', '%s e. CC' % FF('i'), sy(w, AI, iel, 'fzp1elp1', '( i + 1 ) e. %s' % FZN1))
    BODY = '( %s x. ( %s - %s ) )' % (FR('i'), FF('( i + 1 )'), FF('i'))
    bodyc = si([h2, si([fi1c, fic], 'subcld', '( %s - %s ) e. CC' % (FF('( i + 1 )'), FF('i')))], 'mulcld', '%s e. CC' % BODY)
    idi = w.s([], 'id', '( i = N -> i = N )')
    subN, BN = w.congr(BODY, {'i': 'N'}, 'i = N', {'i': idi})
    SM1 = 'sum_ i e. ( 1 ... ( N - 1 ) ) %s' % BODY
    m1 = st([nuz, bodyc, subN], 'fsumm1', '%s = ( %s + %s )' % (SPARTS, SM1, BN))
    fzo = sy(w, PH, nz, 'fzoval', '%s = ( 1 ... ( N - 1 ) )' % FZO)
    SMo = 'sum_ i e. %s %s' % (FZO, BODY)
    rng = st([st([fzo], 'eqcomd', '( 1 ... ( N - 1 ) ) = %s' % FZO)], 'sumeq1d', '%s = %s' % (SM1, SMo))
    # fsumparts on ( 1 ..^ N )
    hb, B, Wj = subh(w, FR('k'), FF('k'), 'i'); hc, Cc, X = subh(w, FR('k'), FF('k'), '( i + 1 )'); hd, D, Y = subh(w, FR('k'), FF('k'), '1'); he, Ee, Z = subh(w, FR('k'), FF('k'), 'N')
    AK = '( ph /\\ k e. %s )' % FZN
    sk = mkst(w, AK)
    rk, _ = rename(w, PH, FZN, 'i', 'k', h2, '%s e. CC' % FR('i'))
    fk0, _ = rename(w, PH, FZN1, 'i', 'k', h3, '%s e. CC' % FF('i'))
    kel1 = sk([sk([clo(w, 'fzssp1', '%s C_ %s' % (FZN, FZN1))], 'a1i', '%s C_ %s' % (FZN, FZN1)), sk([], 'simpr', 'k e. %s' % FZN)], 'sseldd', 'k e. %s' % FZN1)
    fk = hyp2(w, AK, sk([], 'simpl', 'ph'), kel1, fk0, '%s e. CC' % FF('k'))
    SNEG = 'sum_ i e. %s ( ( %s - %s ) x. %s )' % (FZO, Cc, B, X)
    parts = st([hb, hc, hd, he, nuz, rk, fk], 'fsumparts', '%s = ( ( ( %s x. %s ) - ( %s x. %s ) ) - %s )' % (SMo, Ee, Z, D, Y, SNEG))
    AIo, so, f = io_closures(w, h2, h3)
    DR = '( %s - %s )' % (FR('i'), FR('( i + 1 )'))
    TERM = '( %s x. %s )' % (DR, FF('( i + 1 )'))
    neg = so([so([so([f['ri'], f['ri1']], 'negsubdi2d', '-u %s = ( %s - %s )' % (DR, FR('( i + 1 )'), FR('i')))], 'eqcomd', '( %s - %s ) = -u %s' % (FR('( i + 1 )'), FR('i'), DR))], 'oveq1d',
             '( ( %s - %s ) x. %s ) = ( -u %s x. %s )' % (FR('( i + 1 )'), FR('i'), FF('( i + 1 )'), DR, FF('( i + 1 )')))
    drc = so([f['ri'], f['ri1']], 'subcld', '%s e. CC' % DR)
    neg2 = so([neg, so([drc, f['fi1']], 'mulneg1d', '( -u %s x. %s ) = -u %s' % (DR, FF('( i + 1 )'), TERM))], 'eqtrd', '( ( %s - %s ) x. %s ) = -u %s' % (FR('( i + 1 )'), FR('i'), FF('( i + 1 )'), TERM))
    termc = so([drc, f['fi1']], 'mulcld', '%s e. CC' % TERM)
    fino = st([clo(w, 'fzofi', '%s e. Fin' % FZO)], 'a1i', '%s e. Fin' % FZO)
    sneg = eqtr(w, PH, [st([neg2], 'sumeq2dv', '%s = sum_ i e. %s -u %s' % (SNEG, FZO, TERM)), st([fino, termc], 'fsumneg', 'sum_ i e. %s -u %s = -u %s' % (FZO, TERM, SDIFF))], None)
    sdc = st([fino, termc], 'fsumcl', '%s e. CC' % SDIFF)
    rN, fN, fN1, r1, f1 = rf_closures(w, h2, h3, nuz, n1uz)
    P1_ = '( %s x. %s )' % (FR('N'), FF('N')); P2_ = '( %s x. %s )' % (FR('1'), FF('1')); P3_ = '( %s x. %s )' % (FR('N'), FF(N1))
    p1c = st([rN, fN], 'mulcld', '%s e. CC' % P1_); p2c = st([r1, f1], 'mulcld', '%s e. CC' % P2_); p3c = st([rN, fN1], 'mulcld', '%s e. CC' % P3_)
    p12c = st([p1c, p2c], 'subcld', '( %s - %s ) e. CC' % (P1_, P2_))
    smo = eqtr(w, PH, [parts, st([sneg], 'oveq2d', '( ( %s - %s ) - %s ) = ( ( %s - %s ) - -u %s )' % (P1_, P2_, SNEG, P1_, P2_, SDIFF)),
                       st([p12c, sdc], 'subnegd', '( ( %s - %s ) - -u %s ) = ( ( %s - %s ) + %s )' % (P1_, P2_, SDIFF, P1_, P2_, SDIFF))], None)
    bn = st([rN, fN1, fN], 'subdid', '%s = ( %s - %s )' % (BN, P3_, P1_))
    tot = st([m1, st([st([rng, smo], 'eqtrd', '%s = ( ( %s - %s ) + %s )' % (SM1, P1_, P2_, SDIFF)), bn], 'oveq12d',
                      '( %s + %s ) = ( ( ( %s - %s ) + %s ) + ( %s - %s ) )' % (SM1, BN, P1_, P2_, SDIFF, P3_, P1_))], 'eqtrd',
             '%s = ( ( ( %s - %s ) + %s ) + ( %s - %s ) )' % (SPARTS, P1_, P2_, SDIFF, P3_, P1_))
    p31c = st([p3c, p1c], 'subcld', '( %s - %s ) e. CC' % (P3_, P1_))
    alg = eqtr(w, PH, [st([st([p12c, sdc], 'addcomd', '( ( %s - %s ) + %s ) = ( %s + ( %s - %s ) )' % (P1_, P2_, SDIFF, SDIFF, P1_, P2_))], 'oveq1d',
                          '( ( ( %s - %s ) + %s ) + ( %s - %s ) ) = ( ( %s + ( %s - %s ) ) + ( %s - %s ) )' % (P1_, P2_, SDIFF, P3_, P1_, SDIFF, P1_, P2_, P3_, P1_)),
                       st([sdc, p12c, p31c], 'addassd', '( ( %s + ( %s - %s ) ) + ( %s - %s ) ) = ( %s + ( ( %s - %s ) + ( %s - %s ) ) )' % (SDIFF, P1_, P2_, P3_, P1_, SDIFF, P1_, P2_, P3_, P1_)),
                       st([st([p1c, p2c, p3c], 'npncan3d', '( ( %s - %s ) + ( %s - %s ) ) = ( %s - %s )' % (P1_, P2_, P3_, P1_, P3_, P2_))], 'oveq2d',
                          '( %s + ( ( %s - %s ) + ( %s - %s ) ) ) = ( %s + ( %s - %s ) )' % (SDIFF, P1_, P2_, P3_, P1_, SDIFF, P3_, P2_))], None)
    w.qed([tot, alg], 'eqtrd', '( ph -> %s = ( %s + ( %s - %s ) ) )' % (SPARTS, SDIFF, P3_, P2_))
    return w


def bvabellem3():
    w = W('bvabellem3', 'The second-order Abel identity: sum_ n <= N A ( n ) ( G ( n ) - G ( N + 1 ) ) - P F ( N + 1 ) = '
                        'sum_ i < N ( R ( i ) - R ( i + 1 ) ) F ( i + 1 ) + ( R ( N ) - P ) F ( N + 1 ), from bvabellem1 and bvabellem2.')
    h = hyps_of(w, 'bvabellem3')
    h1, hp, h2, h3, h4, h5, h6, h7, h8, h9 = h   # N, P, A, G, R, L, F, Gdiff, Frec, F1
    st = mkst(w, PH)
    nz, nre, ncc, nuz, n1uz = nfacts(w, h1)
    lem1 = st([h1, h2, h3], 'bvabellem1', '%s = %s' % (SABEL, SSWAP))
    AI = '( ph /\\ i e. %s )' % FZN
    si = mkst(w, AI)
    iel = si([], 'simpr', 'i e. %s' % FZN); phi = si([], 'simpl', 'ph')
    asic = asa_cl(w, AI, phi, h2, 'i', sy(w, AI, iel, 'elfzuz3', 'N e. ( ZZ>= ` i )'))
    iel1 = si([si([clo(w, 'fzssp1', '%s C_ %s' % (FZN, FZN1))], 'a1i', '%s C_ %s' % (FZN, FZN1)), iel], 'sseldd', 'i e. %s' % FZN1)
    fic = hyp2(w, AI, phi, iel1, h6, '%s e. CC' % FF('i'))
    LA = '( %s x. %s )' % (FL('i'), ASA('i'))
    lac = si([h5, asic], 'mulcld', '%s e. CC' % LA)
    fd = si([si([h8], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (FF('( i + 1 )'), FF('i'), FF('i'), LA, FF('i'))), si([fic, lac], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (FF('i'), LA, FF('i'), LA))], 'eqtrd',
            '( %s - %s ) = %s' % (FF('( i + 1 )'), FF('i'), LA))
    DG = '( %s - %s )' % (FG('i'), FG('( i + 1 )'))
    body = eqtr(w, AI, [si([h7], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (DG, ASA('i'), FR('i'), FL('i'), ASA('i'))),
                        si([h4, h5, asic], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (FR('i'), FL('i'), ASA('i'), FR('i'), LA)),
                        si([si([fd], 'eqcomd', '%s = ( %s - %s )' % (LA, FF('( i + 1 )'), FF('i')))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s - %s ) )' % (FR('i'), LA, FR('i'), FF('( i + 1 )'), FF('i')))], None)
    sw = st([body], 'sumeq2dv', '%s = %s' % (SSWAP, SPARTS))
    P3_ = '( %s x. %s )' % (FR('N'), FF(N1)); P2_ = '( %s x. %s )' % (FR('1'), FF('1'))
    lem2 = st([h1, h4, h6], 'bvabellem2', '%s = ( %s + ( %s - %s ) )' % (SPARTS, SDIFF, P3_, P2_))
    rN, fN, fN1, r1, f1 = rf_closures(w, h4, h6, nuz, n1uz)
    p3c = st([rN, fN1], 'mulcld', '%s e. CC' % P3_)
    p20 = st([st([h9], 'oveq2d', '%s = ( %s x. 0 )' % (P2_, FR('1'))), st([r1], 'mul01d', '( %s x. 0 ) = 0' % FR('1'))], 'eqtrd', '%s = 0' % P2_)
    AIo, so, f = io_closures(w, h4, h6)
    TERM = '( ( %s - %s ) x. %s )' % (FR('i'), FR('( i + 1 )'), FF('( i + 1 )'))
    termc = so([so([f['ri'], f['ri1']], 'subcld', '( %s - %s ) e. CC' % (FR('i'), FR('( i + 1 )'))), f['fi1']], 'mulcld', '%s e. CC' % TERM)
    fino = st([clo(w, 'fzofi', '%s e. Fin' % FZO)], 'a1i', '%s e. Fin' % FZO)
    sdc = st([fino, termc], 'fsumcl', '%s e. CC' % SDIFF)
    tot = eqtr(w, PH, [lem1, sw, lem2, st([st([st([p20], 'oveq2d', '( %s - %s ) = ( %s - 0 )' % (P3_, P2_, P3_)), st([p3c], 'subid1d', '( %s - 0 ) = %s' % (P3_, P3_))], 'eqtrd',
                                             '( %s - %s ) = %s' % (P3_, P2_, P3_))], 'oveq2d', '( %s + ( %s - %s ) ) = ( %s + %s )' % (SDIFF, P3_, P2_, SDIFF, P3_))], None)
    PF = '( P x. %s )' % FF(N1)
    pfc = st([hp, fN1], 'mulcld', '%s e. CC' % PF)
    c1 = st([tot], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (SABEL, PF, SDIFF, P3_, PF))
    c2 = st([sdc, p3c, pfc], 'addsubassd', '( ( %s + %s ) - %s ) = ( %s + ( %s - %s ) )' % (SDIFF, P3_, PF, SDIFF, P3_, PF))
    c3 = st([st([st([rN, hp, fN1], 'subdird', '( ( %s - P ) x. %s ) = ( %s - %s )' % (FR('N'), FF(N1), P3_, PF))], 'eqcomd', '( %s - %s ) = ( ( %s - P ) x. %s )' % (P3_, PF, FR('N'), FF(N1)))], 'oveq2d',
            '( %s + ( %s - %s ) ) = ( %s + ( ( %s - P ) x. %s ) )' % (SDIFF, P3_, PF, SDIFF, FR('N'), FF(N1)))
    w.qed([eqtr(w, PH, [c1, c2], None), c3], 'eqtrd', '( ph -> ( %s - %s ) = ( %s + ( ( %s - P ) x. %s ) ) )' % (SABEL, PF, SDIFF, FR('N'), FF(N1)))
    return w


def bvabelin():
    w = W('bvabelin', 'The second-order Abel bound: with |F| <= M, R decreasing on ( 1 ... N ) and P <= R ( N ), '
                      '| sum_ n <= N A ( n ) ( G ( n ) - G ( N + 1 ) ) - P F ( N + 1 ) | <= M ( R ( 1 ) - P ).')
    h = hyps_of(w, 'bvabelin')
    h1, hm, hp, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14 = h
    st = mkst(w, PH)
    nz, nre, ncc, nuz, n1uz = nfacts(w, h1)
    # CC forms for bvabellem3
    AN = '( ph /\\ n e. %s )' % FZN; AI = '( ph /\\ i e. %s )' % FZN; AI1 = '( ph /\\ i e. %s )' % FZN1
    cc = lambda ante, step, e: w.s([step], 'recnd', '( %s -> %s e. CC )' % (ante, e))
    pc = cc(PH, hp, 'P'); h4c = cc(AN, h4, FA('n')); h5c = cc(AI1, h5, FG('i')); h6c = cc(AI, h6, FR('i')); h7c = cc(AI, h7, FL('i')); h8c = cc(AI1, h8, FF('i'))
    PF = '( P x. %s )' % FF(N1); XT = '( ( %s - P ) x. %s )' % (FR('N'), FF(N1))
    lem3 = st([h1, pc, h4c, h5c, h6c, h7c, h8c, h9, h10, h11], 'bvabellem3', '( %s - %s ) = ( %s + %s )' % (SABEL, PF, SDIFF, XT))
    # the terms of SDIFF under i e. ( 1 ..^ N )
    AIo, so, f = io_closures(w, h6, h8, kind='RR')
    ri, ri1, fi1 = f['ri'], f['ri1'], f['fi1']
    absle, _ = val_at(w, AIo, h12, FZN1, '( i + 1 )', '( abs ` %s ) <_ M' % FF('i'), f['ip11'])
    DR = '( %s - %s )' % (FR('i'), FR('( i + 1 )'))
    TERM = '( %s x. %s )' % (DR, FF('( i + 1 )'))
    drr = so([ri, ri1], 'resubcld', '%s e. RR' % DR)
    dr0 = so([h13, so([ri, ri1], 'subge0d', '( 0 <_ %s <-> %s <_ %s )' % (DR, FR('( i + 1 )'), FR('i')))], 'mpbird', '0 <_ %s' % DR)
    fi1c = so([fi1], 'recnd', '%s e. CC' % FF('( i + 1 )'))
    termc = so([so([drr], 'recnd', '%s e. CC' % DR), fi1c], 'mulcld', '%s e. CC' % TERM)
    aterm = so([so([so([drr], 'recnd', '%s e. CC' % DR), fi1c], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TERM, DR, FF('( i + 1 )'))),
                so([so([drr, dr0], 'absidd', '( abs ` %s ) = %s' % (DR, DR))], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (DR, FF('( i + 1 )'), DR, FF('( i + 1 )')))], 'eqtrd',
               '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (TERM, DR, FF('( i + 1 )')))
    afr = so([fi1c], 'abscld', '( abs ` %s ) e. RR' % FF('( i + 1 )'))
    mi = lift(w, hm, AIo)
    tle = so([aterm, so([afr, mi, drr, dr0, absle], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. M )' % (DR, FF('( i + 1 )'), DR))], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. M )' % (TERM, DR))
    fino = st([clo(w, 'fzofi', '%s e. Fin' % FZO)], 'a1i', '%s e. Fin' % FZO)
    SABS = 'sum_ i e. %s ( abs ` %s )' % (FZO, TERM); SDM = 'sum_ i e. %s ( %s x. M )' % (FZO, DR); SDR = 'sum_ i e. %s %s' % (FZO, DR)
    fa = st([fino, termc], 'fsumabs', '( abs ` %s ) <_ %s' % (SDIFF, SABS))
    fl = st([fino, so([termc], 'abscld', '( abs ` %s ) e. RR' % TERM), so([drr, mi], 'remulcld', '( %s x. M ) e. RR' % DR), tle], 'fsumle', '%s <_ %s' % (SABS, SDM))
    mc = st([hm], 'recnd', 'M e. CC')
    mul = st([fino, mc, so([drr], 'recnd', '%s e. CC' % DR)], 'fsummulc1', '( %s x. M ) = %s' % (SDR, SDM))
    # telescoping
    t1 = w.s([], 'fveq2', '( k = i -> %s = %s )' % (FR('k'), FR('i'))); t2 = w.s([], 'fveq2', '( k = ( i + 1 ) -> %s = %s )' % (FR('k'), FR('( i + 1 )')))
    t3 = w.s([], 'fveq2', '( k = 1 -> %s = %s )' % (FR('k'), FR('1'))); t4 = w.s([], 'fveq2', '( k = N -> %s = %s )' % (FR('k'), FR('N')))
    rk, _ = rename(w, PH, FZN, 'i', 'k', h6c, '%s e. CC' % FR('i'))
    tel = st([t1, t2, t3, t4, nuz, rk], 'telfsumo', '%s = ( %s - %s )' % (SDR, FR('1'), FR('N')))
    sdm = st([st([mul], 'eqcomd', '%s = ( %s x. M )' % (SDM, SDR)), st([tel], 'oveq1d', '( %s x. M ) = ( ( %s - %s ) x. M )' % (SDR, FR('1'), FR('N')))], 'eqtrd', '%s = ( ( %s - %s ) x. M )' % (SDM, FR('1'), FR('N')))
    # the last term
    memN = sy(w, PH, nuz, 'eluzfz2', 'N e. %s' % FZN); memN1 = sy(w, PH, n1uz, 'eluzfz2', '%s e. %s' % (N1, FZN1)); mem1 = sy(w, PH, nuz, 'eluzfz1', '1 e. %s' % FZN)
    rN, _ = inst(w, PH, FZN, 'i', 'N', h6, '%s e. RR' % FR('i'), memN)
    fN1, _ = inst(w, PH, FZN1, 'i', N1, h8, '%s e. RR' % FF('i'), memN1)
    r1, _ = inst(w, PH, FZN, 'i', '1', h6, '%s e. RR' % FR('i'), mem1)
    aN1, _ = inst(w, PH, FZN1, 'i', N1, h12, '( abs ` %s ) <_ M' % FF('i'), memN1)
    RP = '( %s - P )' % FR('N')
    rpr = st([rN, hp], 'resubcld', '%s e. RR' % RP)
    rp0 = st([h14, st([rN, hp], 'subge0d', '( 0 <_ %s <-> P <_ %s )' % (RP, FR('N')))], 'mpbird', '0 <_ %s' % RP)
    fN1c = st([fN1], 'recnd', '%s e. CC' % FF(N1)); rpc = st([rpr], 'recnd', '%s e. CC' % RP)
    xtc = st([rpc, fN1c], 'mulcld', '%s e. CC' % XT)
    axt = st([st([rpc, fN1c], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (XT, RP, FF(N1))),
              st([st([rpr, rp0], 'absidd', '( abs ` %s ) = %s' % (RP, RP))], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (RP, FF(N1), RP, FF(N1)))], 'eqtrd',
             '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (XT, RP, FF(N1)))
    xle = st([axt, st([st([fN1c], 'abscld', '( abs ` %s ) e. RR' % FF(N1)), hm, rpr, rp0, aN1], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. M )' % (RP, FF(N1), RP))], 'eqbrtrd',
             '( abs ` %s ) <_ ( %s x. M )' % (XT, RP))
    sdc = st([fino, termc], 'fsumcl', '%s e. CC' % SDIFF)
    tri = sy2(w, PH, sdc, xtc, 'abstri', '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SDIFF, XT, SDIFF, XT))
    LHS = '( %s - %s )' % (SABEL, PF)
    tri2 = st([st([lem3], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s + %s ) )' % (LHS, SDIFF, XT)), tri], 'eqbrtrd', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (LHS, SDIFF, XT))
    ALHS = '( abs ` ( %s + %s ) )' % (SDIFF, XT)
    leaves = {ALHS: st([st([sdc, xtc], 'addcld', '( %s + %s ) e. CC' % (SDIFF, XT))], 'abscld', '%s e. RR' % ALHS),
              '( abs ` %s )' % SDIFF: st([sdc], 'abscld', '( abs ` %s ) e. RR' % SDIFF), '( abs ` %s )' % XT: st([xtc], 'abscld', '( abs ` %s ) e. RR' % XT),
              SABS: st([fino, so([termc], 'abscld', '( abs ` %s ) e. RR' % TERM)], 'fsumrecl', '%s e. RR' % SABS),
              SDM: st([fino, so([drr, mi], 'remulcld', '( %s x. M ) e. RR' % DR)], 'fsumrecl', '%s e. RR' % SDM),
              FR('1'): r1, FR('N'): rN, 'P': hp, 'M': hm}
    goal = nlinarith(w, PH, [tri, fa, fl, sdm, xle], '%s <_ ( M x. %s )' % (ALHS, RN1), leaves=leaves)
    w.qed([st([lem3], 'fveq2d', '( abs ` %s ) = %s' % (LHS, ALHS)), goal], 'eqbrtrd', '( ph -> ( abs ` %s ) <_ ( M x. %s ) )' % (LHS, RN1))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvabellem1', 'bvabellem2', 'bvabellem3', 'bvabelin']:
        runh(globals()[f]())
