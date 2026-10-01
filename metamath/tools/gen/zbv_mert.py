"""Sortie ZBV, block Z-MP part 1: elementary lemmas for the Mertens product
(ZeroDensity.lean section 6).

zdmprss       ( ( 1 ... N ) i^i Prime ) C_ ( 2 ... N )
fprodefsumfi  ( ph -> prod_ k e. A ( exp ` B ) = ( exp ` sum_ k e. A B ) )   [A e. Fin]
zdmisq        ( M e. NN -> sum_ n e. ( 2 ... M ) ( ( 1 / n ) ^ 2 ) <_ 1 )
zdminv        ( ( X e. RR /\\ 0 <_ X /\\ X <_ ( 1 / 2 ) ) -> ( 1 / ( 1 - X ) ) <_ ( exp ` ( X + ( 2 x. ( X ^ 2 ) ) ) ) )
zdmlogl1      ( ( Y e. RR /\\ 1 < Y ) -> ( 1 - ( 1 / Y ) ) <_ ( log ` Y ) )
zdmlogl       ( I e. ( ZZ>= ` 2 ) -> ( 1 - ( ( log ` I ) / ( log ` ( I + 1 ) ) ) )
                <_ ( ( log ` ( log ` ( I + 1 ) ) ) - ( log ` ( log ` I ) ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbvlib import *
from lin import linarith, nlinarith, lineq

PR = lambda N: '( ( 1 ... %s ) i^i Prime )' % N


def zdmprss():
    w = W('zdmprss', 'The primes up to N lie in ( 2 ... N ).')
    A = 'p e. %s' % PR('N')
    st = mkst(w, A)
    pin = st([], 'id', A)
    p1 = sy(w, A, pin, 'elinel1', 'p e. ( 1 ... N )')
    pp = sy(w, A, pin, 'elinel2', 'p e. Prime')
    pu = sy(w, A, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )')
    nu = sy(w, A, p1, 'elfzuz3', 'N e. ( ZZ>= ` p )')
    both = st([pu, nu], 'jca', '( p e. ( ZZ>= ` 2 ) /\\ N e. ( ZZ>= ` p ) )')
    bi = clo(w, 'elfzuzb', '( p e. ( 2 ... N ) <-> ( p e. ( ZZ>= ` 2 ) /\\ N e. ( ZZ>= ` p ) ) )')
    el = st([both, st([bi], 'a1i', '( p e. ( 2 ... N ) <-> ( p e. ( ZZ>= ` 2 ) /\\ N e. ( ZZ>= ` p ) ) )')],
            'mpbird', 'p e. ( 2 ... N )')
    w.qed([el], 'ssriv', '%s C_ ( 2 ... N )' % PR('N'))
    return w


def fprodefsumfi():
    w = W('fprodefsumfi', 'A finite product of exponentials is the exponential of the sum, over '
                          'any finite index set (fprodefsum through a bijection with an '
                          'initial segment).')
    h1 = hyp(w, '1', 'fprodefsumfi.1', '( ph -> A e. Fin )')
    h2 = hyp(w, '2', 'fprodefsumfi.2', '( ( ph /\\ k e. A ) -> ( F ` k ) e. CC )')
    N = '( # ` A )'
    BIJ = 'f : ( 1 ... %s ) -1-1-onto-> A' % N
    LHS = 'prod_ k e. A ( exp ` ( F ` k ) )'; RHS = '( exp ` sum_ k e. A ( F ` k ) )'
    GOAL = '%s = %s' % (LHS, RHS)
    cases = w.s([h1, w.inst('fz1f1o')], 'syl',
                '( ph -> ( A = (/) \\/ ( %s e. NN /\\ E. f %s ) ) )' % (N, BIJ))
    # case 1
    A1 = '( ph /\\ A = (/) )'
    s1 = mkst(w, A1)
    ae = s1([], 'simpr', 'A = (/)')
    p0 = s1([s1([ae], 'prodeq1d', '%s = prod_ k e. (/) ( exp ` ( F ` k ) )' % LHS),
             s1([clo(w, 'prod0', 'prod_ k e. (/) ( exp ` ( F ` k ) ) = 1')], 'a1i',
                'prod_ k e. (/) ( exp ` ( F ` k ) ) = 1')], 'eqtrd', '%s = 1' % LHS)
    su0 = s1([s1([ae], 'sumeq1d', 'sum_ k e. A ( F ` k ) = sum_ k e. (/) ( F ` k )'),
              s1([clo(w, 'sum0', 'sum_ k e. (/) ( F ` k ) = 0')], 'a1i', 'sum_ k e. (/) ( F ` k ) = 0')], 'eqtrd',
             'sum_ k e. A ( F ` k ) = 0')
    e0 = s1([s1([su0], 'fveq2d', '%s = ( exp ` 0 )' % RHS), s1([clo(w, 'ef0', '( exp ` 0 ) = 1')], 'a1i',
                                                              '( exp ` 0 ) = 1')], 'eqtrd', '%s = 1' % RHS)
    c1 = s1([p0, e0], 'eqtr4d', GOAL)
    # case 2
    A2 = '( ph /\\ %s e. NN )' % N
    A3 = '( %s /\\ %s )' % (A2, BIJ)
    s3 = mkst(w, A3)
    nnn = s3([], 'simplr', '%s e. NN' % N)
    bij = s3([], 'simpr', BIJ)
    FV = '( F ` ( f ` n ) )'
    FZ = '( 1 ... %s )' % N
    sub1 = w.s([], '2fveq3', '( k = ( f ` n ) -> ( exp ` ( F ` k ) ) = ( exp ` %s ) )' % FV)
    fin = s3([], 'fzfid', '%s e. Fin' % FZ)
    AN = '( %s /\\ n e. %s )' % (A3, FZ)
    sn = mkst(w, AN)
    fv = sn([], 'eqidd', '( f ` n ) = ( f ` n )')
    h2l = adlr(w, adlr(w, h2, '%s e. NN' % N), BIJ)
    AK = '( %s /\\ k e. A )' % A3
    sk = mkst(w, AK)
    ebc = sk([h2l], 'efcld', '( exp ` ( F ` k ) ) e. CC')
    pf = s3([sub1, fin, bij, fv, ebc], 'fprodf1o', '%s = prod_ n e. %s ( exp ` %s )' % (LHS, FZ, FV))
    sub2 = w.s([], 'fveq2', '( k = ( f ` n ) -> ( F ` k ) = %s )' % FV)
    sf = s3([sub2, fin, bij, fv, h2l], 'fsumf1o', 'sum_ k e. A ( F ` k ) = sum_ n e. %s %s' % (FZ, FV))
    # closure of the value on ( 1 ... N )
    nel = sn([], 'simpr', 'n e. %s' % FZ)
    fnA = sn([sy(w, AN, lift(w, bij, AN), 'f1of', 'f : %s --> A' % FZ), nel], 'ffvelcdmd', '( f ` n ) e. A')
    fvc, _ = inst(w, AN, 'A', 'k', '( f ` n )', adlr(w, h2l, 'n e. %s' % FZ), '( F ` k ) e. CC', fnA)
    # the if-extended body for fprodefsum, which needs closure on all of NN
    C = 'if ( n e. %s , %s , 0 )' % (FZ, FV)
    ceq = sn([nel], 'iftrued', '%s = %s' % (C, FV))
    pe1 = s3([ceq], 'prodeq2dv', 'prod_ n e. %s %s = prod_ n e. %s %s' % (FZ, '( exp ` %s )' % C, FZ, '( exp ` %s )' % FV)) if False else None
    ceqe = sn([ceq], 'fveq2d', '( exp ` %s ) = ( exp ` %s )' % (C, FV))
    pe1 = s3([ceqe], 'prodeq2dv', 'prod_ n e. %s ( exp ` %s ) = prod_ n e. %s ( exp ` %s )' % (FZ, C, FZ, FV))
    se1 = s3([ceq], 'sumeq2dv', 'sum_ n e. %s %s = sum_ n e. %s %s' % (FZ, C, FZ, FV))
    ANN = '( %s /\\ n e. NN )' % A3
    snn = mkst(w, ANN)
    AT = '( %s /\\ n e. %s )' % (ANN, FZ)
    stt = mkst(w, AT)
    ct = stt([stt([stt([], 'simpr', 'n e. %s' % FZ)], 'iftrued', '%s = %s' % (C, FV)),
              lift(w, fvc, AT) if False else stt([lift(w, s3([], 'id', A3) if False else bij, AT)], 'id', BIJ) if False else None], 'x', 'y') if False else None
    # ( ( A3 /\ n e. NN ) /\ n e. FZ ) -> C e. CC : from fvc lifted by ( A3 /\ n e. FZ ) ~ reorder
    fvc2 = w.s([fvc], 'adantlr', '( ( ( %s /\\ n e. NN ) /\\ n e. %s ) -> %s e. CC )' % (A3, FZ, FV))
    ct = stt([stt([stt([], 'simpr', 'n e. %s' % FZ)], 'iftrued', '%s = %s' % (C, FV)), fvc2], 'eqeltrd', '%s e. CC' % C)
    AF = '( %s /\\ -. n e. %s )' % (ANN, FZ)
    sf_ = mkst(w, AF)
    cf = sf_([sf_([sf_([], 'simpr', '-. n e. %s' % FZ)], 'iffalsed', '%s = 0' % C), sf_([], '0cnd', '0 e. CC')], 'eqeltrd',
             '%s e. CC' % C)
    ccl = snn([ct, cf], 'pm2.61dan', '%s e. CC' % C)
    z = clo(w, 'nnuz', NNUZ)
    nz = s3([nnn, s3([z], 'a1i', NNUZ)], 'eleqtrd', '%s e. ( ZZ>= ` 1 )' % N)
    pe = s3([z, nnn, ccl], 'fprodefsum', 'prod_ n e. %s ( exp ` %s ) = ( exp ` sum_ n e. %s %s )' % (FZ, C, FZ, C))
    pe2 = s3([s3([pe1], 'eqcomd', 'prod_ n e. %s ( exp ` %s ) = prod_ n e. %s ( exp ` %s )' % (FZ, FV, FZ, C)),
              s3([pe, s3([se1], 'fveq2d', '( exp ` sum_ n e. %s %s ) = ( exp ` sum_ n e. %s %s )' % (FZ, C, FZ, FV))], 'eqtrd',
                 'prod_ n e. %s ( exp ` %s ) = ( exp ` sum_ n e. %s %s )' % (FZ, C, FZ, FV))], 'eqtrd',
             'prod_ n e. %s ( exp ` %s ) = ( exp ` sum_ n e. %s %s )' % (FZ, FV, FZ, FV))
    c3 = s3([s3([pf, pe2], 'eqtrd', '%s = ( exp ` sum_ n e. %s %s )' % (LHS, FZ, FV)),
             s3([sf], 'fveq2d', '%s = ( exp ` sum_ n e. %s %s )' % (RHS, FZ, FV))], 'eqtr4d', GOAL)
    c3e = w.s([c3], 'ex', '( %s -> ( %s -> %s ) )' % (A2, BIJ, GOAL))
    c3x = w.s([c3e], 'exlimdv', '( %s -> ( E. f %s -> %s ) )' % (A2, BIJ, GOAL))
    c3i = w.s([c3x], 'imp', '( ( %s /\\ E. f %s ) -> %s )' % (A2, BIJ, GOAL))
    c2 = w.s([c3i], 'anasss', '( ( ph /\\ ( %s e. NN /\\ E. f %s ) ) -> %s )' % (N, BIJ, GOAL))
    w.qed([c1, c2, cases], 'mpjaodan', '( ph -> %s )' % GOAL)
    return w


def zdmisq():
    w = W('zdmisq', 'The sum of the reciprocal squares from 2 to M is at most 1 (from telsum).')
    A = 'M e. NN'
    st = mkst(w, A)
    AN = '( %s /\\ n e. ( 2 ... M ) )' % A
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. ( 2 ... M )')
    nrp = sy(w, AN, nel, 'fz2m1rp', '( n x. ( n - 1 ) ) e. RR+')
    nz = sy(w, AN, nel, 'elfzelz', 'n e. ZZ')
    nre = sn([nz], 'zred', 'n e. RR')
    ncc = sn([nre], 'recnd', 'n e. CC')
    n2le = sy(w, AN, nel, 'elfzle1', '2 <_ n')
    npos = linarith(w, AN, [n2le], '0 < n', leaves={'n': nre})
    nrp2 = sn([nre, npos], 'elrpd', 'n e. RR+')
    nne0 = sn([nrp2], 'rpne0d', 'n =/= 0')
    rec = sn([ncc, nne0, sn([], '2z', '2 e. ZZ' ) if False else sn([clo(w, '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'),
              w.inst('exprec')], 'syl3anc', '( ( 1 / n ) ^ 2 ) = ( 1 / ( n ^ 2 ) )')
    sq = sn([ncc], 'sqvald', '( n ^ 2 ) = ( n x. n )')
    nm1 = sn([nre, sn([], '1red', '1 e. RR')], 'resubcld', '( n - 1 ) e. RR')
    le1 = sn([nre], 'lem1d', '( n - 1 ) <_ n')
    nge0 = sn([nrp2], 'rpge0d', '0 <_ n')
    mle = sn([nm1, nre, nre, nge0, le1], 'lemul2ad', '( n x. ( n - 1 ) ) <_ ( n x. n )')
    mle2 = sn([mle, sq], 'breqtrrd', '( n x. ( n - 1 ) ) <_ ( n ^ 2 )')
    n2rp = sn([nrp2, sn([clo(w, '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld', '( n ^ 2 ) e. RR+')
    lr = sn([sn([nrp], 'rpregt0d', '( ( n x. ( n - 1 ) ) e. RR /\\ 0 < ( n x. ( n - 1 ) ) )'),
             sn([n2rp], 'rpregt0d', '( ( n ^ 2 ) e. RR /\\ 0 < ( n ^ 2 ) )'), w.inst('lerec')], 'syl2anc',
            '( ( n x. ( n - 1 ) ) <_ ( n ^ 2 ) <-> ( 1 / ( n ^ 2 ) ) <_ ( 1 / ( n x. ( n - 1 ) ) ) )')
    rle = sn([mle2, lr], 'mpbid', '( 1 / ( n ^ 2 ) ) <_ ( 1 / ( n x. ( n - 1 ) ) )')
    tle = sn([rec, rle], 'eqbrtrd', '( ( 1 / n ) ^ 2 ) <_ ( 1 / ( n x. ( n - 1 ) ) )')
    b1 = sn([sn([nrp2], 'rprecred', '( 1 / n ) e. RR')], 'resqcld', '( ( 1 / n ) ^ 2 ) e. RR')
    b2 = sn([nrp], 'rprecred', '( 1 / ( n x. ( n - 1 ) ) ) e. RR')
    fin = st([], 'fzfid', '( 2 ... M ) e. Fin')
    sle = st([fin, b1, b2, tle], 'fsumle',
             'sum_ n e. ( 2 ... M ) ( ( 1 / n ) ^ 2 ) <_ sum_ n e. ( 2 ... M ) ( 1 / ( n x. ( n - 1 ) ) )')
    cb = w.s([w.s([w.s([w.s([], 'id', '( n = j -> n = j )'), w.s([], 'oveq1', '( n = j -> ( n - 1 ) = ( j - 1 ) )')],
                       'oveq12d', '( n = j -> ( n x. ( n - 1 ) ) = ( j x. ( j - 1 ) ) )')], 'oveq2d',
                  '( n = j -> ( 1 / ( n x. ( n - 1 ) ) ) = ( 1 / ( j x. ( j - 1 ) ) ) )')], 'cbvsumv',
             'sum_ n e. ( 2 ... M ) ( 1 / ( n x. ( n - 1 ) ) ) = sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) )')
    ts = st([], 'telsum', 'sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) ) <_ 1')
    ts2 = st([st([cb], 'a1i', 'sum_ n e. ( 2 ... M ) ( 1 / ( n x. ( n - 1 ) ) ) = sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) )'), ts],
             'eqbrtrd', 'sum_ n e. ( 2 ... M ) ( 1 / ( n x. ( n - 1 ) ) ) <_ 1')
    r1 = st([fin, b1], 'fsumrecl', 'sum_ n e. ( 2 ... M ) ( ( 1 / n ) ^ 2 ) e. RR')
    r2 = st([fin, b2], 'fsumrecl', 'sum_ n e. ( 2 ... M ) ( 1 / ( n x. ( n - 1 ) ) ) e. RR')
    w.qed([r1, r2, st([], '1red', '1 e. RR'), sle, ts2], 'letrd',
          '( %s -> sum_ n e. ( 2 ... M ) ( ( 1 / n ) ^ 2 ) <_ 1 )' % A)
    return w


def zdminv():
    w = W('zdminv', 'The reciprocal of 1 - X is at most exp ( X + 2 X ^ 2 ) for 0 <= X <= 1/2 '
                    '(Lean inv_one_sub_le_exp).')
    A = '( X e. RR /\\ 0 <_ X /\\ X <_ ( 1 / 2 ) )'
    st = mkst(w, A)
    xr = st([], 'simp1', 'X e. RR'); x0 = st([], 'simp2', '0 <_ X'); xh = st([], 'simp3', 'X <_ ( 1 / 2 )')
    xc = st([xr], 'recnd', 'X e. CC')
    one = st([], '1red', '1 e. RR'); onec = st([], '1cnd', '1 e. CC')
    mx = st([one, xr], 'resubcld', '( 1 - X ) e. RR')
    mxpos = linarith(w, A, [xh], '0 < ( 1 - X )', leaves={'X': xr})
    mxrp = st([mx, mxpos], 'elrpd', '( 1 - X ) e. RR+')
    mxc = st([mx], 'recnd', '( 1 - X ) e. CC'); mxne = st([mxrp], 'rpne0d', '( 1 - X ) =/= 0')
    Y = '( X / ( 1 - X ) )'
    yr = st([xr, mxrp], 'rerpdivcld', '%s e. RR' % Y)
    y0 = st([xr, mxrp, x0], 'divge0d', '0 <_ %s' % Y)
    # 1 / ( 1 - X ) = 1 + Y
    e1 = st([onec, xc], 'npcand', '( ( 1 - X ) + X ) = 1')
    e2 = st([mxc, xc, mxc, mxne], 'divdird', '( ( ( 1 - X ) + X ) / ( 1 - X ) ) = ( ( ( 1 - X ) / ( 1 - X ) ) + %s )' % Y)
    e3 = st([mxc, mxne], 'dividd', '( ( 1 - X ) / ( 1 - X ) ) = 1')
    e4 = st([e3], 'oveq1d', '( ( ( 1 - X ) / ( 1 - X ) ) + %s ) = ( 1 + %s )' % (Y, Y))
    e5 = st([e1], 'oveq1d', '( ( ( 1 - X ) + X ) / ( 1 - X ) ) = ( 1 / ( 1 - X ) )')
    rec = st([st([e5, e2], 'eqtr3d', '( 1 / ( 1 - X ) ) = ( ( ( 1 - X ) / ( 1 - X ) ) + %s )' % Y), e4], 'eqtrd',
             '( 1 / ( 1 - X ) ) = ( 1 + %s )' % Y)
    # 1 + Y <_ exp Y
    py = st([one, yr], 'readdcld', '( 1 + %s ) e. RR' % Y)
    py1 = linarith(w, A, [y0], '1 <_ ( 1 + %s )' % Y, leaves={Y: yr})
    lg = st([py, py1, w.inst('extrwlogle')], 'syl2anc', '( log ` ( 1 + %s ) ) <_ ( ( 1 + %s ) - 1 )' % (Y, Y))
    pc = st([onec, st([yr], 'recnd', '%s e. CC' % Y)], 'pncan2d', '( ( 1 + %s ) - 1 ) = %s' % (Y, Y))
    lg2 = st([lg, pc], 'breqtrd', '( log ` ( 1 + %s ) ) <_ %s' % (Y, Y))
    pyrp = st([py, linarith(w, A, [y0], '0 < ( 1 + %s )' % Y, leaves={Y: yr})], 'elrpd', '( 1 + %s ) e. RR+' % Y)
    lgr = st([pyrp], 'relogcld', '( log ` ( 1 + %s ) ) e. RR' % Y)
    ef1 = st([st([lgr, yr, w.inst('efle')], 'syl2anc',
                 '( ( log ` ( 1 + %s ) ) <_ %s <-> ( exp ` ( log ` ( 1 + %s ) ) ) <_ ( exp ` %s ) )' % (Y, Y, Y, Y)), lg2],
             'mpbi' if False else 'mpbird', '( exp ` ( log ` ( 1 + %s ) ) ) <_ ( exp ` %s )' % (Y, Y)) if False else None
    efbi = st([lgr, yr, w.inst('efle')], 'syl2anc',
              '( ( log ` ( 1 + %s ) ) <_ %s <-> ( exp ` ( log ` ( 1 + %s ) ) ) <_ ( exp ` %s ) )' % (Y, Y, Y, Y))
    ef1 = st([lg2, efbi], 'mpbid', '( exp ` ( log ` ( 1 + %s ) ) ) <_ ( exp ` %s )' % (Y, Y))
    rl = st([pyrp, w.inst('reeflog')], 'syl', '( exp ` ( log ` ( 1 + %s ) ) ) = ( 1 + %s )' % (Y, Y))
    ef2 = st([rl, ef1], 'eqbrtrrd', '( 1 + %s ) <_ ( exp ` %s )' % (Y, Y))
    # Y <_ X + 2 X^2
    Q = '( X + ( 2 x. ( X ^ 2 ) ) )'
    x2 = st([xr], 'resqcld', '( X ^ 2 ) e. RR')
    qr = st([xr, st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), x2], 'remulcld', '( 2 x. ( X ^ 2 ) ) e. RR')],
            'readdcld', '%s e. RR' % Q)
    goal = 'X <_ ( ( 1 - X ) x. %s )' % Q
    nl = nlinarith(w, A, [x0, xh], goal, leaves={'X': xr})
    dbi = st([xr, qr, mxrp], 'ledivmuld', '( %s <_ %s <-> X <_ ( ( 1 - X ) x. %s ) )' % (Y, Q, Q))
    yle = st([nl, dbi], 'mpbird', '%s <_ %s' % (Y, Q))
    efbi2 = st([yr, qr, w.inst('efle')], 'syl2anc', '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (Y, Q, Y, Q))
    ef3 = st([yle, efbi2], 'mpbid', '( exp ` %s ) <_ ( exp ` %s )' % (Y, Q))
    ey = st([yr], 'reefcld', '( exp ` %s ) e. RR' % Y)
    eq = st([qr], 'reefcld', '( exp ` %s ) e. RR' % Q)
    ch = st([py, ey, eq, ef2, ef3], 'letrd', '( 1 + %s ) <_ ( exp ` %s )' % (Y, Q))
    w.qed([rec, ch], 'eqbrtrd', '( %s -> ( 1 / ( 1 - X ) ) <_ ( exp ` %s ) )' % (A, Q))
    return w


def zdmlogl1():
    w = W('zdmlogl1', 'The logarithm is at least 1 - 1 / Y for Y > 1 (from logdiflbnd).')
    A = '( Y e. RR /\\ 1 < Y )'
    st = mkst(w, A)
    yr = st([], 'simpl', 'Y e. RR'); y1 = st([], 'simpr', '1 < Y')
    yc = st([yr], 'recnd', 'Y e. CC')
    one = st([], '1red', '1 e. RR'); onec = st([], '1cnd', '1 e. CC')
    ym = st([yr, one], 'resubcld', '( Y - 1 ) e. RR')
    ympos = st([y1, st([one, yr], 'posdifd', '( 1 < Y <-> 0 < ( Y - 1 ) )')], 'mpbid', '0 < ( Y - 1 )')
    ymrp = st([ym, ympos], 'elrpd', '( Y - 1 ) e. RR+')
    ymc = st([ym], 'recnd', '( Y - 1 ) e. CC'); ymne = st([ymrp], 'rpne0d', '( Y - 1 ) =/= 0')
    yrp = st([yr, st([one, yr, st([clo(w, '0lt1', '0 < 1')], 'a1i', '0 < 1'), y1], 'lttrd' if False else 'lttrd', '0 < Y') if False else
              linarith(w, A, [y1], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+')
    yne = st([yrp], 'rpne0d', 'Y =/= 0')
    AA = '( 1 / ( Y - 1 ) )'
    arp = st([ymrp], 'rpreccld', '%s e. RR+' % AA)
    ac = st([arp], 'rpcnd', '%s e. CC' % AA); ane = st([arp], 'rpne0d', '%s =/= 0' % AA)
    ld = st([arp, w.inst('logdiflbnd')], 'syl',
            '( 1 / ( %s + 1 ) ) <_ ( ( log ` ( %s + 1 ) ) - ( log ` %s ) )' % (AA, AA, AA))
    # A + 1 = Y / ( Y - 1 )
    d1 = st([ymc, ymne], 'dividd', '( ( Y - 1 ) / ( Y - 1 ) ) = 1')
    d2 = st([onec, ymc, ymc, ymne], 'divdird', '( ( 1 + ( Y - 1 ) ) / ( Y - 1 ) ) = ( %s + ( ( Y - 1 ) / ( Y - 1 ) ) )' % AA)
    d3 = st([onec, yc], 'pncan3d', '( 1 + ( Y - 1 ) ) = Y')
    d4 = st([d3], 'oveq1d', '( ( 1 + ( Y - 1 ) ) / ( Y - 1 ) ) = ( Y / ( Y - 1 ) )')
    d5 = st([d1], 'oveq2d', '( %s + ( ( Y - 1 ) / ( Y - 1 ) ) ) = ( %s + 1 )' % (AA, AA))
    ap1 = st([st([d4, d2], 'eqtr3d', '( Y / ( Y - 1 ) ) = ( %s + ( ( Y - 1 ) / ( Y - 1 ) ) )' % AA), d5], 'eqtrd',
             '( Y / ( Y - 1 ) ) = ( %s + 1 )' % AA)
    # 1 / ( A + 1 ) = 1 - 1 / Y
    r1 = st([ap1], 'oveq2d', '( 1 / ( Y / ( Y - 1 ) ) ) = ( 1 / ( %s + 1 ) )' % AA)
    r2 = st([yc, ymc, yne, ymne], 'recdivd', '( 1 / ( Y / ( Y - 1 ) ) ) = ( ( Y - 1 ) / Y )')
    r3 = st([yc, onec, yc, yne], 'divsubdird', '( ( Y - 1 ) / Y ) = ( ( Y / Y ) - ( 1 / Y ) )')
    r4 = st([st([yc, yne], 'dividd', '( Y / Y ) = 1')], 'oveq1d', '( ( Y / Y ) - ( 1 / Y ) ) = ( 1 - ( 1 / Y ) )')
    lhs = st([st([r1, r2], 'eqtr3d', '( 1 / ( %s + 1 ) ) = ( ( Y - 1 ) / Y )' % AA),
              st([r3, r4], 'eqtrd', '( ( Y - 1 ) / Y ) = ( 1 - ( 1 / Y ) )')], 'eqtrd',
             '( 1 / ( %s + 1 ) ) = ( 1 - ( 1 / Y ) )' % AA)
    # log ( A + 1 ) - log A = log Y
    ap1rp = st([yrp, ymrp], 'rpdivcld', '( Y / ( Y - 1 ) ) e. RR+')
    ap1rp2 = st([ap1, ap1rp], 'eqeltrrd', '( %s + 1 ) e. RR+' % AA)
    ld1 = st([ap1rp2, arp, w.inst('relogdiv')], 'syl2anc',
             '( log ` ( ( %s + 1 ) / %s ) ) = ( ( log ` ( %s + 1 ) ) - ( log ` %s ) )' % (AA, AA, AA, AA))
    q1 = st([ap1], 'oveq1d', '( ( Y / ( Y - 1 ) ) / %s ) = ( ( %s + 1 ) / %s )' % (AA, AA, AA))
    q2 = st([st([yc, ymc, yne if False else ymne], 'divcld', '( Y / ( Y - 1 ) ) e. CC'), ymc, ymne], 'divrecd' if False else 'divrecd',
            '( ( Y / ( Y - 1 ) ) / %s ) = ( ( Y / ( Y - 1 ) ) x. ( 1 / %s ) )' % (AA, AA)) if False else None
    # ( Y / ( Y - 1 ) ) / ( 1 / ( Y - 1 ) ) = ( Y / ( Y - 1 ) ) x. ( Y - 1 ) = Y
    qc = st([yc, ymc, ymne], 'divcld', '( Y / ( Y - 1 ) ) e. CC')
    q2 = st([qc, ac, ane], 'divrecd', '( ( Y / ( Y - 1 ) ) / %s ) = ( ( Y / ( Y - 1 ) ) x. ( 1 / %s ) )' % (AA, AA))
    q3 = st([st([ymc, ymne], 'recrecd', '( 1 / %s ) = ( Y - 1 )' % AA)], 'oveq2d',
            '( ( Y / ( Y - 1 ) ) x. ( 1 / %s ) ) = ( ( Y / ( Y - 1 ) ) x. ( Y - 1 ) )' % AA)
    q4 = st([yc, ymc, ymne], 'divcan1d', '( ( Y / ( Y - 1 ) ) x. ( Y - 1 ) ) = Y')
    qe = st([st([q2, q3], 'eqtrd', '( ( Y / ( Y - 1 ) ) / %s ) = ( ( Y / ( Y - 1 ) ) x. ( Y - 1 ) )' % AA), q4], 'eqtrd',
            '( ( Y / ( Y - 1 ) ) / %s ) = Y' % AA)
    qe2 = st([q1, qe], 'eqtr3d', '( ( %s + 1 ) / %s ) = Y' % (AA, AA))
    rhs = st([st([qe2], 'fveq2d', '( log ` ( ( %s + 1 ) / %s ) ) = ( log ` Y )' % (AA, AA)), ld1], 'eqtr3d',
             '( log ` Y ) = ( ( log ` ( %s + 1 ) ) - ( log ` %s ) )' % (AA, AA))
    w.qed([ld, lhs, st([rhs], 'eqcomd', '( ( log ` ( %s + 1 ) ) - ( log ` %s ) ) = ( log ` Y )' % (AA, AA))], '3brtr3d',
          '( %s -> ( 1 - ( 1 / Y ) ) <_ ( log ` Y ) )' % A)
    return w


def zdmlogl():
    w = W('zdmlogl', 'The step 1 - log I / log ( I + 1 ) is at most the increment of log log '
                     '(Lean one_sub_div_log_le).')
    A = 'I e. ( ZZ>= ` 2 )'
    st = mkst(w, A)
    iu = st([], 'id', A)
    ir = sy(w, A, iu, 'eluzelre', 'I e. RR')
    i1 = st([iu], 'eluz2gt1' if False else 'eluz2gt1', '1 < I') if False else st([iu, w.inst('eluz2gt1')], 'syl', '1 < I')
    one = st([], '1red', '1 e. RR')
    ip = st([ir, one], 'readdcld', '( I + 1 ) e. RR')
    ip1 = linarith(w, A, [i1], '1 < ( I + 1 )', leaves={'I': ir})
    LA = '( log ` I )'; LB = '( log ` ( I + 1 ) )'
    arp = st([ir, i1, w.inst('rplogcl')], 'syl2anc', '%s e. RR+' % LA)
    brp = st([ip, ip1, w.inst('rplogcl')], 'syl2anc', '%s e. RR+' % LB)
    ar = st([arp], 'rpred', '%s e. RR' % LA); br = st([brp], 'rpred', '%s e. RR' % LB)
    irp = st([ir, linarith(w, A, [i1], '0 < I', leaves={'I': ir})], 'elrpd', 'I e. RR+')
    iprp = st([ip, linarith(w, A, [i1], '0 < ( I + 1 )', leaves={'I': ir})], 'elrpd', '( I + 1 ) e. RR+')
    ilt = st([ir], 'ltp1d', 'I < ( I + 1 )')
    ablt = st([ilt, st([irp, iprp, w.inst('logltb')], 'syl2anc', '( I < ( I + 1 ) <-> %s < %s )' % (LA, LB))],
              'mpbid', '%s < %s' % (LA, LB))
    Y = '( %s / %s )' % (LB, LA)
    yr = st([br, arp], 'rerpdivcld', '%s e. RR' % Y)
    m1 = st([st([arp], 'rpcnd', '%s e. CC' % LA)], 'mullidd', '( 1 x. %s ) = %s' % (LA, LA))
    lt1 = st([m1, ablt], 'eqbrtrd', '( 1 x. %s ) < %s' % (LA, LB))
    y1 = st([lt1, st([one, br, arp], 'ltmuldivd', '( ( 1 x. %s ) < %s <-> 1 < %s )' % (LA, LB, Y))], 'mpbid', '1 < %s' % Y)
    core = st([yr, y1, w.inst('zdmlogl1')], 'syl2anc', '( 1 - ( 1 / %s ) ) <_ ( log ` %s )' % (Y, Y))
    rd = st([st([brp], 'rpcnd', '%s e. CC' % LB), st([arp], 'rpcnd', '%s e. CC' % LA),
             st([brp], 'rpne0d', '%s =/= 0' % LB), st([arp], 'rpne0d', '%s =/= 0' % LA)], 'recdivd',
            '( 1 / %s ) = ( %s / %s )' % (Y, LA, LB))
    lhs = st([rd], 'oveq2d', '( 1 - ( 1 / %s ) ) = ( 1 - ( %s / %s ) )' % (Y, LA, LB))
    rhs = st([brp, arp, w.inst('relogdiv')], 'syl2anc', '( log ` %s ) = ( ( log ` %s ) - ( log ` %s ) )' % (Y, LB, LA))
    w.qed([lhs, rhs, core], '3brtr3d',
          '( %s -> ( 1 - ( %s / %s ) ) <_ ( ( log ` %s ) - ( log ` %s ) ) )' % (A, LA, LB, LB, LA))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['zdmprss', 'fprodefsumfi', 'zdmisq', 'zdminv', 'zdmlogl1', 'zdmlogl']:
        wk = globals()[f]()
        (runh(wk) if f in ('fprodefsumfi',) else wk.run())
