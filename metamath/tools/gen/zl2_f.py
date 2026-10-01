"""ZL2 section F: the interpolated Gamma-factor bound, generic (LConvexity 518-736: zl2gint).
`MM_DB=sorties/zl2.mm python3 tools/gen/zl2_f.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import *
from lin import linarith, nlinarith
from zl1lib import mptv as mptval_
from zl2_p import strip_mem, inst_ral, ebounds
import num

only = sys.argv[1:]
SKIP = set()          # worksheet line indices the local-variable rename leaves alone


def inst_ral_y(w, ante, ralst, S, body, mem):
    """( ante -> body[z:=y] ) from ralst: ( ante -> A. z e. S body ) and mem: ( ante -> y e. S );
    the congruence lines carry the real substitution z := y and are exempt from rename_local"""
    n0 = len(w.lines)
    idx = w.s([], 'id', '( z = y -> z = y )')
    st, val = w.wcongr(body, {'z': 'y'}, 'z = y', {'z': idx})
    r = w.s([st], 'rspcv', '( y e. %s -> ( A. z e. %s %s -> %s ) )' % (S, S, body, val))
    SKIP.update(range(n0, len(w.lines)))
    return w.s([mem, ralst, r], 'sylc', '( %s -> %s )' % (ante, val)), val


def rename_local(w, protect):
    """the strip variable of the proof is y, not z: the antecedent binds z in its quantified
    hypotheses (protect), so ralrimiva / rspcv need a fresh letter"""
    keys = ['@P%d@' % i for i in range(len(protect))]
    for i, line in enumerate(w.lines):
        if i in SKIP or ' |- ' not in line:
            continue
        head, f = line.split(' |- ', 1)
        for k, t in zip(keys, protect):
            f = f.replace(t, k)
        f = (' ' + f + ' ').replace(' z ', ' y ')[1:-1]
        for k, t in zip(keys, protect):
            f = f.replace(k, t)
        w.lines[i] = head + ' |- ' + f


def gauss3(w, A, Eb, er, wr, izr, iwr, sqle):
    """( A -> ( exp ` ( ( ( Eb - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` z ) - ( Im ` W ) ) ^ 2 ) ) ) <_ ( 3 x. ( exp ` -u ( ( ( Im ` z ) - ( Im ` W ) ) ^ 2 ) ) ) )
    from sqle: ( A -> ( ( Eb - ( Re ` W ) ) ^ 2 ) <_ 1 )"""
    a = '( ( %s - ( Re ` W ) ) ^ 2 )' % Eb
    V = '( ( Im ` z ) - ( Im ` W ) )'
    b = '( %s ^ 2 )' % V
    ar = D(w, A, 'resqcld', [D(w, A, 'resubcld', [er, wr], '( %s - ( Re ` W ) ) e. RR' % Eb)], '%s e. RR' % a)
    vr = D(w, A, 'resubcld', [izr, iwr], '%s e. RR' % V)
    br = D(w, A, 'resqcld', [vr], '%s e. RR' % b)
    ac = D(w, A, 'recnd', [ar], '%s e. CC' % a)
    bc = D(w, A, 'recnd', [br], '%s e. CC' % b)
    e1 = w.s([w.s([ac, bc], 'negsubd', '( %s -> ( %s + -u %s ) = ( %s - %s ) )' % (A, a, b, a, b))], 'eqcomd',
             '( %s -> ( %s - %s ) = ( %s + -u %s ) )' % (A, a, b, a, b))
    e2 = E(w, A, 'fveq2d', [e1], '( exp ` ( %s - %s ) )' % (a, b), '( exp ` ( %s + -u %s ) )' % (a, b))
    e3 = efadd_(w, A, a, '-u %s' % b, ac, D(w, A, 'negcld', [bc], '-u %s e. CC' % b))
    eq = w.s([e2, e3], 'eqtrd', '( %s -> ( exp ` ( %s - %s ) ) = ( ( exp ` %s ) x. ( exp ` -u %s ) ) )' % (A, a, b, a, b))
    one = a1(w, A, '1re', '1 e. RR')
    le1 = efle_(w, A, a, '1', ar, one, sqle)
    e13 = w.s([e1le3(w)], 'a1i', '( %s -> ( exp ` 1 ) <_ 3 )' % A)
    ea = D(w, A, 'reefcld', [ar], '( exp ` %s ) e. RR' % a)
    le3 = D(w, A, 'letrd', [ea, D(w, A, 'reefcld', [one], '( exp ` 1 ) e. RR'), a1(w, A, '3re', '3 e. RR'), le1, e13], '( exp ` %s ) <_ 3' % a)
    nb = D(w, A, 'renegcld', [br], '-u %s e. RR' % b)
    enb = D(w, A, 'reefcld', [nb], '( exp ` -u %s ) e. RR' % b)
    enb0 = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), enb, w.s([nb, w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` -u %s ) )' % (A, b))], '0 <_ ( exp ` -u %s )' % b)
    m = D(w, A, 'lemul1ad', [ea, a1(w, A, '3re', '3 e. RR'), enb, enb0, le3], '( ( exp ` %s ) x. ( exp ` -u %s ) ) <_ ( 3 x. ( exp ` -u %s ) )' % (a, b, b))
    return w.s([eq, m], 'eqbrtrd', '( %s -> ( exp ` ( %s - %s ) ) <_ ( 3 x. ( exp ` -u %s ) ) )' % (A, a, b, b)), enb, enb0


# ---------------------------------------------------------------- zl2gint
if __name__ == '__main__' and (not only or 'zl2gint' in only):
    w = W('zl2gint', 'The interpolated Gamma-factor bound, generic: a function holomorphic on the strip ` -1/2 <_ Re z <_ 0 ` , '
          'bounded by ` 3 ( 2 + | z | ) ` on ` Re z = -1/2 ` and by ` 3 ( | Im z | + 2 ) ^ ( 1 / 2 ) ` on ` Re z = 0 ` , is bounded by '
          '` 34 ( | Im w | + 2 ) ^ ( 1/2 - Re w ) ` inside ( ~ zl2pln with ` C = log q ` ; Lean ` norm_Gamma_one_sub_mul_sin_interp ` ).')
    A = STATEMENTS['zl2gint'].split(' -> ( abs ` ( F ` W ) )')[0][2:]
    assert A == '( %s /\\ ( W e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 ) ) )' % GINT, A
    S = STRG
    gi = D(w, A, 'simpl', [], GINT)
    h3 = D(w, A, 'simpll', [], '( ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) /\\ %s )' % (S, GRWB('F', S)))
    lines = D(w, A, 'simplr', [], '( %s )' % GINT.split(' ) /\\ ( ', 1)[1][:-2]) if False else None
    LM = 'A. z e. CC ( ( Re ` z ) = -u ( 1 / 2 ) -> ( abs ` ( F ` z ) ) <_ ( 3 x. ( 2 + ( abs ` z ) ) ) )'
    L0 = 'A. z e. CC ( ( Re ` z ) = 0 -> ( abs ` ( F ` z ) ) <_ ( 3 x. ( ( ( abs ` ( Im ` z ) ) + 2 ) ^c ( 1 / 2 ) ) ) )'
    lm = D(w, A, 'simplrl' if False else 'simplr', [], '( %s /\\ %s )' % (LM, L0))
    lmm = D(w, A, 'simpld', [lm], LM)
    l00 = D(w, A, 'simprd', [lm], L0)
    wc = D(w, A, 'simprl', [], 'W e. CC')
    wlo = D(w, A, 'simprrl' if False else 'simprr', [], '( -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 )')
    w1 = D(w, A, 'simpld', [wlo], '-u ( 1 / 2 ) <_ ( Re ` W )')
    w2 = D(w, A, 'simprd', [wlo], '( Re ` W ) <_ 0')
    wr = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    iwr = D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')
    nh = w.s([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'renegcli', '-u ( 1 / 2 ) e. RR')], 'a1i', '( %s -> -u ( 1 / 2 ) e. RR )' % A)
    z0 = a1(w, A, '0re', '0 e. RR')
    ws = w.s([w.s([wc, w.s([wr, w1, w2], '3jca', '( %s -> ( ( Re ` W ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 ) )' % A),
                   w.s([nh, z0, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` W ) e. ( -u ( 1 / 2 ) [,] 0 ) <-> ( ( Re ` W ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 ) ) )' % A)],
                  'mpbird' if False else 'jca', 'x')], 'idi', 'x') if False else None
    ric = w.s([w.s([wr, w1, w2], '3jca', '( %s -> ( ( Re ` W ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 ) )' % A),
               w.s([nh, z0, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` W ) e. ( -u ( 1 / 2 ) [,] 0 ) <-> ( ( Re ` W ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 ) ) )' % A)],
              'mpbird', '( %s -> ( Re ` W ) e. ( -u ( 1 / 2 ) [,] 0 ) )' % A)
    ws = w.s([w.s([wc, ric], 'jca', '( %s -> ( W e. CC /\\ ( Re ` W ) e. ( -u ( 1 / 2 ) [,] 0 ) ) )' % A),
              w.s([], 'elstr', '( W e. %s <-> ( W e. CC /\\ ( Re ` W ) e. ( -u ( 1 / 2 ) [,] 0 ) ) )' % S)], 'sylibr', '( %s -> W e. %s )' % (A, S))
    # q and the constants
    Qd = '( ( abs ` ( Im ` W ) ) + 2 )'
    aiw = D(w, A, 'abscld', [D(w, A, 'recnd', [iwr], '( Im ` W ) e. CC')], '( abs ` ( Im ` W ) ) e. RR')
    aiw0 = D(w, A, 'absge0d', [D(w, A, 'recnd', [iwr], '( Im ` W ) e. CC')], '0 <_ ( abs ` ( Im ` W ) )')
    qr = D(w, A, 'readdcld', [aiw, a1(w, A, '2re', '2 e. RR')], '%s e. RR' % Qd)
    cl = Closure(w, A, {'( abs ` ( Im ` W ) )': ('RR', aiw)})
    qp = linarith(w, A, [aiw0], '0 < %s' % Qd, closure=cl)
    qrp = D(w, A, 'elrpd', [qr, qp], '%s e. RR+' % Qd)
    LQ = '( log ` %s )' % Qd
    lqr = D(w, A, 'relogcld', [qrp], '%s e. RR' % LQ)
    R = '( %s ^c ( 1 / 2 ) )' % Qd
    half = a1(w, A, 'halfre', '( 1 / 2 ) e. RR')
    rrp = D(w, A, 'rpcxpcld', [qrp, half], '%s e. RR+' % R)
    QQ = '( ; 3 4 x. %s )' % R
    n34 = w.s([w.s([w.s([], '3nn0', '3 e. NN0'), w.s([], '4nn', '4 e. NN')], 'decnncl', '; 3 4 e. NN'), w.s([], 'nnrp', '( ; 3 4 e. NN -> ; 3 4 e. RR+ )')], 'ax-mp', '; 3 4 e. RR+')
    qqrp = D(w, A, 'rpmulcld', [w.s([n34], 'a1i', '( %s -> ; 3 4 e. RR+ )' % A), rrp], '%s e. RR+' % QQ)
    gr = D(w, A, 'simprd', [h3], GRWB('F', S))
    hol3 = D(w, A, 'simpld', [h3], '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D )' % S)
    # the line bounds, as zl2pln wants them, at X = -1/2, Y = 0, P = 0, C = log q, Q = 34 q ^ ( 1 / 2 )
    Az = '( %s /\\ z e. %s )' % (A, S)
    zs = D(w, Az, 'simpr', [], 'z e. %s' % S)
    zc, zr, zlo, zhi = strip_mem(w, Az, 'z', zs, w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), w.s([z0], 'adantr', '( %s -> 0 e. RR )' % Az), X='-u ( 1 / 2 )', Y='0')
    izr = D(w, Az, 'imcld', [zc], '( Im ` z ) e. RR')
    wrz = w.s([wr], 'adantr', '( %s -> ( Re ` W ) e. RR )' % Az)
    iwrz = w.s([iwr], 'adantr', '( %s -> ( Im ` W ) e. RR )' % Az)
    w1z = w.s([w1], 'adantr', '( %s -> -u ( 1 / 2 ) <_ ( Re ` W ) )' % Az)
    w2z = w.s([w2], 'adantr', '( %s -> ( Re ` W ) <_ 0 )' % Az)
    V = '( ( Im ` z ) - ( Im ` W ) )'
    DV = '( abs ` %s )' % V
    vr = D(w, Az, 'resubcld', [izr, iwrz], '%s e. RR' % V)
    dvr = D(w, Az, 'abscld', [D(w, Az, 'recnd', [vr], '%s e. CC' % V)], '%s e. RR' % DV)
    dv0 = D(w, Az, 'absge0d', [D(w, Az, 'recnd', [vr], '%s e. CC' % V)], '0 <_ %s' % DV)
    tab = w.s([izr, iwrz, w.inst('zl2tab')], 'syl2anc', '( %s -> ( ( abs ` ( Im ` z ) ) + 2 ) <_ ( %s x. ( 1 + %s ) ) )' % (Az, Qd, DV))
    H = '( exp ` -u ( %s ^ 2 ) )' % V
    U = '( ( 1 + %s ) x. %s )' % (DV, H)
    gau = w.s([vr, w.inst('zl2gau')], 'syl', '( %s -> %s <_ 3 )' % (Az, U))
    qrz = w.s([qr], 'adantr', '( %s -> %s e. RR )' % (Az, Qd))
    qrpz = w.s([qrp], 'adantr', '( %s -> %s e. RR+ )' % (Az, Qd))
    rrz = w.s([D(w, A, 'rpred', [rrp], '%s e. RR' % R)], 'adantr', '( %s -> %s e. RR )' % (Az, R))
    r0z = w.s([D(w, A, 'rpge0d', [rrp], '0 <_ %s' % R)], 'adantr', '( %s -> 0 <_ %s )' % (Az, R))
    fz = w.s([w.s([w.s([w.s([hol3], 'simp1d' if False else 'idi', 'x')], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    fcn = D(w, A, 'simp1d', [hol3], 'F e. ( D -cn-> CC )')
    sd = D(w, A, 'simp3d', [hol3], '%s C_ D' % S)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A)
    zd = w.s([w.s([sd], 'adantr', '( %s -> %s C_ D )' % (Az, S)), zs], 'sseldd', '( %s -> z e. D )' % Az)
    fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Az), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % Az)
    afz = D(w, Az, 'abscld', [fzc], '( abs ` ( F ` z ) ) e. RR')
    afz0 = D(w, Az, 'absge0d', [fzc], '0 <_ ( abs ` ( F ` z ) )')
    lqz = w.s([lqr], 'adantr', '( %s -> %s e. RR )' % (Az, LQ))
    # --- edge Re z = -1/2
    Ae = '( %s /\\ ( Re ` z ) = -u ( 1 / 2 ) )' % Az
    L = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Ae, f))
    rze = D(w, Ae, 'simpr', [], '( Re ` z ) = -u ( 1 / 2 )')
    fb, _ = inst_ral_y(w, Ae, w.s([lmm], 'ad2antrr', '( %s -> %s )' % (Ae, LM)), 'CC', LM[len('A. z e. CC '):], L(zc, 'z e. CC'))
    fb1 = w.s([fb, rze], 'mpd', '( %s -> ( abs ` ( F ` z ) ) <_ ( 3 x. ( 2 + ( abs ` z ) ) ) )' % Ae)
    acr = w.s([L(zc, 'z e. CC'), w.inst('abscrle')], 'syl', '( %s -> ( abs ` z ) <_ ( ( abs ` ( Re ` z ) ) + ( abs ` ( Im ` z ) ) ) )' % Ae)
    arz = D(w, Ae, 'abscld', [D(w, Ae, 'recnd', [L(zr, '( Re ` z ) e. RR')], '( Re ` z ) e. CC')], '( abs ` ( Re ` z ) ) e. RR')
    nb_ = ebounds(w, Ae, '( Re ` z )', L(zr, '( Re ` z ) e. RR'))
    # | Re z | = 1/2: from Re z = -1/2
    are = w.s([w.s([rze], 'fveq2d', '( %s -> ( abs ` ( Re ` z ) ) = ( abs ` -u ( 1 / 2 ) ) )' % Ae),
               w.s([w.s([w.s([w.s([], 'halfcn', '( 1 / 2 ) e. CC')], 'absnegi', '( abs ` -u ( 1 / 2 ) ) = ( abs ` ( 1 / 2 ) )'),
                         w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([w.s([], 'halfgt0', '0 < ( 1 / 2 )'), ], 'idi' if False else 'ltlei' if False else 'idi', '0 < ( 1 / 2 )')], 'idi', 'x') if False else
                         w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halfgt0', '0 < ( 1 / 2 )')], 'ltleii', '0 <_ ( 1 / 2 )'),
                              w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'absidi', '( 0 <_ ( 1 / 2 ) -> ( abs ` ( 1 / 2 ) ) = ( 1 / 2 ) )')],
                             'ax-mp', '( abs ` ( 1 / 2 ) ) = ( 1 / 2 )')], 'eqtri', '( abs ` -u ( 1 / 2 ) ) = ( 1 / 2 )')],
                   'a1i', '( %s -> ( abs ` -u ( 1 / 2 ) ) = ( 1 / 2 ) )' % Ae)], 'eqtrd', '( %s -> ( abs ` ( Re ` z ) ) = ( 1 / 2 ) )' % Ae)
    azr = D(w, Ae, 'abscld', [L(zc, 'z e. CC')], '( abs ` z ) e. RR')
    aizr = D(w, Ae, 'abscld', [D(w, Ae, 'recnd', [L(izr, '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '( abs ` ( Im ` z ) ) e. RR')
    aiz0 = D(w, Ae, 'absge0d', [D(w, Ae, 'recnd', [L(izr, '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '0 <_ ( abs ` ( Im ` z ) )')
    T = '( %s x. ( 1 + %s ) )' % (Qd, DV)
    Tr = D(w, Ae, 'remulcld', [L(qrz, '%s e. RR' % Qd), D(w, Ae, 'readdcld', [a1(w, Ae, '1re', '1 e. RR'), L(dvr, '%s e. RR' % DV)], '( 1 + %s ) e. RR' % DV)], '%s e. RR' % T)
    cle = Closure(w, Ae, {'( abs ` ( F ` z ) )': ('RR', L(afz, '( abs ` ( F ` z ) ) e. RR')), '( abs ` z )': ('RR', azr), '( abs ` ( Re ` z ) )': ('RR', arz),
                          '( abs ` ( Im ` z ) )': ('RR', aizr), T: ('RR', Tr)})
    cle.atom(T)
    fb2 = linarith(w, Ae, [fb1, acr, are, L(tab, '( ( abs ` ( Im ` z ) ) + 2 ) <_ %s' % T), aiz0], '( abs ` ( F ` z ) ) <_ ( ( ; 1 5 / 4 ) x. %s )' % T, closure=cle)
    # the Gaussian factor
    sqle = nlinarith(w, Ae, [L(w1z, '-u ( 1 / 2 ) <_ ( Re ` W )'), L(w2z, '( Re ` W ) <_ 0')], '( ( -u ( 1 / 2 ) - ( Re ` W ) ) ^ 2 ) <_ 1',
                     leaves={'( Re ` W )': L(wrz, '( Re ` W ) e. RR')})
    G1, enb, enb0 = gauss3(w, Ae, '-u ( 1 / 2 )', w.s([nh], 'a1i' if False else 'adantr', 'x') if False else L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR'),
                           L(wrz, '( Re ` W ) e. RR'), L(izr, '( Im ` z ) e. RR'), L(iwrz, '( Im ` W ) e. RR'), sqle)
    # the power factor: e ^ ( ( -1/2 - 0 ) log q ) = q ^ -1/2
    PW = '( %s ^c -u ( 1 / 2 ) )' % Qd
    s0 = D(w, Ae, 'subid1d', [D(w, Ae, 'recnd', [L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR')], '-u ( 1 / 2 ) e. CC')], '( -u ( 1 / 2 ) - 0 ) = -u ( 1 / 2 )')
    p1 = E(w, Ae, 'fveq2d', [E(w, Ae, 'oveq1d', [s0], '( ( -u ( 1 / 2 ) - 0 ) x. %s )' % LQ, '( -u ( 1 / 2 ) x. %s )' % LQ)],
           '( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) )' % LQ, '( exp ` ( -u ( 1 / 2 ) x. %s ) )' % LQ)
    qce = D(w, Ae, 'rpcnd', [L(qrpz, '%s e. RR+' % Qd)], '%s e. CC' % Qd)
    qne = D(w, Ae, 'rpne0d', [L(qrpz, '%s e. RR+' % Qd)], '%s =/= 0' % Qd)
    p2 = D(w, Ae, 'cxpefd', [qce, qne, D(w, Ae, 'recnd', [L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR')], '-u ( 1 / 2 ) e. CC')],
           '%s = ( exp ` ( -u ( 1 / 2 ) x. %s ) )' % (PW, LQ))
    pe = w.s([p1, p2], 'eqtr4d', '( %s -> ( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) ) = %s )' % (Ae, LQ, PW))
    pwr = D(w, Ae, 'rpcxpcld', [L(qrpz, '%s e. RR+' % Qd), L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR')], '%s e. RR+' % PW)
    # q x. q ^ -1/2 = q ^ 1/2
    qpw = D(w, Ae, 'cxpaddd', [qce, qne, a1(w, Ae, 'ax-1cn', '1 e. CC'), D(w, Ae, 'recnd', [L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR')], '-u ( 1 / 2 ) e. CC')],
            '( %s ^c ( 1 + -u ( 1 / 2 ) ) ) = ( ( %s ^c 1 ) x. %s )' % (Qd, Qd, PW))
    hh = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], 'halfcn', '( 1 / 2 ) e. CC')], 'negsubi', '( 1 + -u ( 1 / 2 ) ) = ( 1 - ( 1 / 2 ) )'),
                   w.s([], '1mhlfehlf', '( 1 - ( 1 / 2 ) ) = ( 1 / 2 )')], 'eqtri', '( 1 + -u ( 1 / 2 ) ) = ( 1 / 2 )')], 'a1i', '( %s -> ( 1 + -u ( 1 / 2 ) ) = ( 1 / 2 ) )' % Ae)
    qpw2 = w.s([w.s([w.s([hh], 'oveq2d', '( %s -> ( %s ^c ( 1 + -u ( 1 / 2 ) ) ) = %s )' % (Ae, Qd, R)), qpw], 'eqtr3d',
                    '( %s -> %s = ( ( %s ^c 1 ) x. %s ) )' % (Ae, R, Qd, PW)),
                w.s([D(w, Ae, 'cxp1d', [qce], '( %s ^c 1 ) = %s' % (Qd, Qd))], 'oveq1d', '( %s -> ( ( %s ^c 1 ) x. %s ) = ( %s x. %s ) )' % (Ae, Qd, PW, Qd, PW))],
               'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (Ae, R, Qd, PW))
    # assemble the left edge
    GL = '( exp ` ( ( ( -u ( 1 / 2 ) - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) )' % V
    glr = D(w, Ae, 'reefcld', [D(w, Ae, 'resubcld', [D(w, Ae, 'resqcld', [D(w, Ae, 'resubcld', [L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR'), L(wrz, '( Re ` W ) e. RR')],
                                                                              '( -u ( 1 / 2 ) - ( Re ` W ) ) e. RR')], '( ( -u ( 1 / 2 ) - ( Re ` W ) ) ^ 2 ) e. RR'),
                                                   D(w, Ae, 'resqcld', [L(vr, '%s e. RR' % V)], '( %s ^ 2 ) e. RR' % V)],
                                   '( ( ( -u ( 1 / 2 ) - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) e. RR' % V)], '%s e. RR' % GL)
    gl0 = D(w, Ae, 'ltled', [a1(w, Ae, '0re', '0 e. RR'), glr, w.s([D(w, Ae, 'resubcld', [D(w, Ae, 'resqcld', [D(w, Ae, 'resubcld', [L(w.s([nh], 'adantr', '( %s -> -u ( 1 / 2 ) e. RR )' % Az), '-u ( 1 / 2 ) e. RR'), L(wrz, '( Re ` W ) e. RR')],
                                                                              '( -u ( 1 / 2 ) - ( Re ` W ) ) e. RR')], '( ( -u ( 1 / 2 ) - ( Re ` W ) ) ^ 2 ) e. RR'),
                                                   D(w, Ae, 'resqcld', [L(vr, '%s e. RR' % V)], '( %s ^ 2 ) e. RR' % V)],
                                   '( ( ( -u ( 1 / 2 ) - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) e. RR' % V), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (Ae, GL))], '0 <_ %s' % GL)
    c15 = w.s([w.s([], '1nn0' if False else 'idi', 'x')], 'idi', 'x') if False else None
    F15 = '( ( ; 1 5 / 4 ) x. %s )' % T
    f15r = D(w, Ae, 'remulcld', [num.real(w, '( ; 1 5 / 4 )') if False else w.s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '5nn0', '5 e. NN0')], 'deccl', '; 1 5 e. NN0')], 'nn0rei', '; 1 5 e. RR'),
                                                                                     w.s([], '4re', '4 e. RR'), w.s([], '4ne0', '4 =/= 0')], 'redivcli', '( ; 1 5 / 4 ) e. RR')], 'a1i', '( %s -> ( ; 1 5 / 4 ) e. RR )' % Ae), Tr], '%s e. RR' % F15)
    H3 = '( 3 x. %s )' % H
    h3r = D(w, Ae, 'remulcld', [a1(w, Ae, '3re', '3 e. RR'), L(enb, '%s e. RR' % H) if False else enb], '%s e. RR' % H3)
    m1 = D(w, Ae, 'lemul12ad', [L(afz, '( abs ` ( F ` z ) ) e. RR'), f15r, glr, h3r, L(afz0, '0 <_ ( abs ` ( F ` z ) )'), gl0, fb2, G1],
           '( ( abs ` ( F ` z ) ) x. %s ) <_ ( %s x. %s )' % (GL, F15, H3))
    m2 = D(w, Ae, 'lemul1ad', [D(w, Ae, 'remulcld', [L(afz, '( abs ` ( F ` z ) ) e. RR'), glr], '( ( abs ` ( F ` z ) ) x. %s ) e. RR' % GL),
                               D(w, Ae, 'remulcld', [f15r, h3r], '( %s x. %s ) e. RR' % (F15, H3)), D(w, Ae, 'rpred', [pwr], '%s e. RR' % PW),
                               D(w, Ae, 'rpge0d', [pwr], '0 <_ %s' % PW), m1],
           '( ( ( abs ` ( F ` z ) ) x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s )' % (GL, PW, F15, H3, PW))
    aiwz = w.s([aiw], 'adantr', '( %s -> ( abs ` ( Im ` W ) ) e. RR )' % Az)
    cln = Closure(w, Ae, {'( abs ` ( Im ` W ) )': ('RR', L(aiwz, '( abs ` ( Im ` W ) ) e. RR')), Qd: ('RR', L(qrz, '%s e. RR' % Qd)), DV: ('RR', L(dvr, '%s e. RR' % DV)), H: ('RR', enb), PW: ('RR', D(w, Ae, 'rpred', [pwr], '%s e. RR' % PW)),
                          R: ('RR', L(rrz, '%s e. RR' % R))})
    qpw0 = D(w, Ae, 'mulge0d', [L(qrz, '%s e. RR' % Qd), D(w, Ae, 'rpred', [pwr], '%s e. RR' % PW), D(w, Ae, 'rpge0d', [L(qrpz, '%s e. RR+' % Qd)], '0 <_ %s' % Qd),
                                D(w, Ae, 'rpge0d', [pwr], '0 <_ %s' % PW)], '0 <_ ( %s x. %s )' % (Qd, PW))
    m3 = nlinarith(w, Ae, [L(gau, '%s <_ 3' % U), qpw0, qpw2, L(r0z, '0 <_ %s' % R)], '( ( %s x. %s ) x. %s ) <_ ( ; 3 4 x. %s )' % (F15, H3, PW, R), closure=cln)
    edgeL = w.s([m2, m3], 'letrd' if False else 'idi', 'x') if False else None
    lhsr = D(w, Ae, 'remulcld', [D(w, Ae, 'remulcld', [L(afz, '( abs ` ( F ` z ) ) e. RR'), glr], '( ( abs ` ( F ` z ) ) x. %s ) e. RR' % GL), D(w, Ae, 'rpred', [pwr], '%s e. RR' % PW)],
             '( ( ( abs ` ( F ` z ) ) x. %s ) x. %s ) e. RR' % (GL, PW))
    midr = D(w, Ae, 'remulcld', [D(w, Ae, 'remulcld', [f15r, h3r], '( %s x. %s ) e. RR' % (F15, H3)), D(w, Ae, 'rpred', [pwr], '%s e. RR' % PW)],
             '( ( %s x. %s ) x. %s ) e. RR' % (F15, H3, PW))
    eL = D(w, Ae, 'letrd', [lhsr, midr, w.s([D(w, A, 'rpred', [qqrp], '%s e. RR' % QQ)], 'ad2antrr', '( %s -> %s e. RR )' % (Ae, QQ)), m2, m3],
           '( ( ( abs ` ( F ` z ) ) x. %s ) x. %s ) <_ %s' % (GL, PW, QQ))
    eL2 = w.s([w.s([pe], 'oveq2d', '( %s -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) ) ) = ( ( ( abs ` ( F ` z ) ) x. %s ) x. %s ) )'
                                  % (Ae, GL, LQ, GL, PW)), eL], 'eqbrtrd',
              '( %s -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) ) ) <_ %s )' % (Ae, GL, LQ, QQ))
    exL = w.s([eL2], 'ex', '( %s -> ( ( Re ` z ) = -u ( 1 / 2 ) -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) ) ) <_ %s ) )' % (Az, GL, LQ, QQ))
    LXs = PLNL('-u ( 1 / 2 )')
    SUBS = lambda t: t.replace('( X [,] Y )', '( -u ( 1 / 2 ) [,] 0 )').replace('( ( ( -u ( 1 / 2 ) - P ) x. C )', '( ( ( -u ( 1 / 2 ) - 0 ) x. %s )' % LQ).replace(' <_ Q )', ' <_ %s )' % QQ)
    rL = w.s([exL], 'ralrimiva', '( %s -> A. z e. %s ( ( Re ` z ) = -u ( 1 / 2 ) -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) ) ) <_ %s ) )'
             % (A, S, GL, LQ, QQ))
    # --- edge Re z = 0
    A0e = '( %s /\\ ( Re ` z ) = 0 )' % Az
    L0_ = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A0e, f))
    rz0 = D(w, A0e, 'simpr', [], '( Re ` z ) = 0')
    gb, _ = inst_ral_y(w, A0e, w.s([l00], 'ad2antrr', '( %s -> %s )' % (A0e, L0)), 'CC', L0[len('A. z e. CC '):], L0_(zc, 'z e. CC'))
    gb1 = w.s([gb, rz0], 'mpd', '( %s -> ( abs ` ( F ` z ) ) <_ ( 3 x. ( ( ( abs ` ( Im ` z ) ) + 2 ) ^c ( 1 / 2 ) ) ) )' % A0e)
    I2 = '( ( abs ` ( Im ` z ) ) + 2 )'
    aizr0 = D(w, A0e, 'abscld', [D(w, A0e, 'recnd', [L0_(izr, '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '( abs ` ( Im ` z ) ) e. RR')
    aiz00 = D(w, A0e, 'absge0d', [D(w, A0e, 'recnd', [L0_(izr, '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '0 <_ ( abs ` ( Im ` z ) )')
    i2r = D(w, A0e, 'readdcld', [aizr0, a1(w, A0e, '2re', '2 e. RR')], '%s e. RR' % I2)
    cl0 = Closure(w, A0e, {'( abs ` ( Im ` W ) )': ('RR', L0_(w.s([aiw], 'adantr', '( %s -> ( abs ` ( Im ` W ) ) e. RR )' % Az), '( abs ` ( Im ` W ) ) e. RR')), '( abs ` ( Im ` z ) )': ('RR', aizr0), DV: ('RR', L0_(dvr, '%s e. RR' % DV)), Qd: ('RR', L0_(qrz, '%s e. RR' % Qd))})
    i20 = linarith(w, A0e, [aiz00], '0 <_ %s' % I2, closure=cl0)
    T0r = D(w, A0e, 'remulcld', [L0_(qrz, '%s e. RR' % Qd), D(w, A0e, 'readdcld', [a1(w, A0e, '1re', '1 e. RR'), L0_(dvr, '%s e. RR' % DV)], '( 1 + %s ) e. RR' % DV)], '%s e. RR' % T)
    q00 = D(w, A0e, 'rpge0d', [L0_(qrpz, '%s e. RR+' % Qd)], '0 <_ %s' % Qd)
    d1r = D(w, A0e, 'readdcld', [a1(w, A0e, '1re', '1 e. RR'), L0_(dvr, '%s e. RR' % DV)], '( 1 + %s ) e. RR' % DV)
    d10 = linarith(w, A0e, [L0_(dv0, '0 <_ %s' % DV)], '0 <_ ( 1 + %s )' % DV, closure=cl0)
    d11 = linarith(w, A0e, [L0_(dv0, '0 <_ %s' % DV)], '1 <_ ( 1 + %s )' % DV, closure=cl0)
    T00 = D(w, A0e, 'mulge0d', [L0_(qrz, '%s e. RR' % Qd), d1r, q00, d10], '0 <_ %s' % T)
    hp = a1(w, A0e, 'halfre', '( 1 / 2 ) e. RR')
    hrp = w.s([w.s([w.s([], 'halfgt0', '0 < ( 1 / 2 )'), w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'idi' if False else 'pm3.2i', '( 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) e. RR )')], 'idi', 'x') if False else None
    hrp = w.s([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halfgt0', '0 < ( 1 / 2 )')], 'elrpii', '( 1 / 2 ) e. RR+')], 'a1i', '( %s -> ( 1 / 2 ) e. RR+ )' % A0e)
    c2m = w.s([L0_(tab, '%s <_ %s' % (I2, T)), D(w, A0e, 'cxple2d', [i2r, i20, T0r, T00, hrp], '( %s <_ %s <-> ( %s ^c ( 1 / 2 ) ) <_ ( %s ^c ( 1 / 2 ) ) )' % (I2, T, I2, T))],
              'mpbid', '( %s -> ( %s ^c ( 1 / 2 ) ) <_ ( %s ^c ( 1 / 2 ) ) )' % (A0e, I2, T))
    mc = D(w, A0e, 'mulcxpd', [L0_(qrz, '%s e. RR' % Qd), q00, d1r, d10, a1(w, A0e, 'halfcn', '( 1 / 2 ) e. CC')],
           '( %s ^c ( 1 / 2 ) ) = ( %s x. ( ( 1 + %s ) ^c ( 1 / 2 ) ) )' % (T, R, DV))
    D1H = '( ( 1 + %s ) ^c ( 1 / 2 ) )' % DV
    ple = w.s([w.s([d1r, d11], 'jca', '( %s -> ( ( 1 + %s ) e. RR /\\ 1 <_ ( 1 + %s ) ) )' % (A0e, DV, DV)),
               w.s([hp, a1(w, A0e, '1re', '1 e. RR')], 'jca', '( %s -> ( ( 1 / 2 ) e. RR /\\ 1 e. RR ) )' % A0e),
               w.s([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], '1re', '1 e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'ltleii', '( 1 / 2 ) <_ 1')], 'a1i', '( %s -> ( 1 / 2 ) <_ 1 )' % A0e), w.inst('cxplea')], 'syl3anc',
              '( %s -> %s <_ ( ( 1 + %s ) ^c 1 ) )' % (A0e, D1H, DV))
    ple2 = w.s([ple, D(w, A0e, 'cxp1d', [D(w, A0e, 'recnd', [d1r], '( 1 + %s ) e. CC' % DV)], '( ( 1 + %s ) ^c 1 ) = ( 1 + %s )' % (DV, DV))], 'breqtrd',
               '( %s -> %s <_ ( 1 + %s ) )' % (A0e, D1H, DV))
    d1hr = D(w, A0e, 'recxpcld', [d1r, d10, hp], '%s e. RR' % D1H)
    rr0 = L0_(rrz, '%s e. RR' % R)
    pm = D(w, A0e, 'lemul2ad', [d1hr, d1r, rr0, L0_(r0z, '0 <_ %s' % R), ple2], '( %s x. %s ) <_ ( %s x. ( 1 + %s ) )' % (R, D1H, R, DV))
    i2h = D(w, A0e, 'recxpcld', [i2r, i20, hp], '( %s ^c ( 1 / 2 ) ) e. RR' % I2)
    t0h = D(w, A0e, 'recxpcld', [T0r, T00, hp], '( %s ^c ( 1 / 2 ) ) e. RR' % T)
    RD1 = '( %s x. ( 1 + %s ) )' % (R, DV)
    rd1r = D(w, A0e, 'remulcld', [rr0, d1r], '%s e. RR' % RD1)
    cl0.leaf('( %s ^c ( 1 / 2 ) )' % I2, 'RR', i2h); cl0.leaf('( %s ^c ( 1 / 2 ) )' % T, 'RR', t0h); cl0.leaf('( %s x. %s )' % (R, D1H), 'RR', D(w, A0e, 'remulcld', [rr0, d1hr], '( %s x. %s ) e. RR' % (R, D1H)))
    cl0.leaf(RD1, 'RR', rd1r); cl0.atom(RD1); cl0.atom('( %s x. %s )' % (R, D1H))
    cl0.leaf('( abs ` ( F ` z ) )', 'RR', L0_(afz, '( abs ` ( F ` z ) ) e. RR'))
    gb2 = linarith(w, A0e, [gb1, c2m, mc, pm], '( abs ` ( F ` z ) ) <_ ( 3 x. %s )' % RD1, closure=cl0)
    sqle0 = nlinarith(w, A0e, [L0_(w1z, '-u ( 1 / 2 ) <_ ( Re ` W )'), L0_(w2z, '( Re ` W ) <_ 0')], '( ( 0 - ( Re ` W ) ) ^ 2 ) <_ 1',
                      leaves={'( Re ` W )': L0_(wrz, '( Re ` W ) e. RR')})
    G0, enb_, enb0_ = gauss3(w, A0e, '0', a1(w, A0e, '0re', '0 e. RR'), L0_(wrz, '( Re ` W ) e. RR'), L0_(izr, '( Im ` z ) e. RR'), L0_(iwrz, '( Im ` W ) e. RR'), sqle0)
    G0T = '( exp ` ( ( ( 0 - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) )' % V
    g0in = D(w, A0e, 'resubcld', [D(w, A0e, 'resqcld', [D(w, A0e, 'resubcld', [a1(w, A0e, '0re', '0 e. RR'), L0_(wrz, '( Re ` W ) e. RR')], '( 0 - ( Re ` W ) ) e. RR')],
                                    '( ( 0 - ( Re ` W ) ) ^ 2 ) e. RR'), D(w, A0e, 'resqcld', [L0_(vr, '%s e. RR' % V)], '( %s ^ 2 ) e. RR' % V)],
             '( ( ( 0 - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) e. RR' % V)
    g0r = D(w, A0e, 'reefcld', [g0in], '%s e. RR' % G0T)
    g00 = D(w, A0e, 'ltled', [a1(w, A0e, '0re', '0 e. RR'), g0r, w.s([g0in, w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A0e, G0T))], '0 <_ %s' % G0T)
    RD13 = '( 3 x. %s )' % RD1
    m01 = D(w, A0e, 'lemul12ad', [L0_(afz, '( abs ` ( F ` z ) ) e. RR'), D(w, A0e, 'remulcld', [a1(w, A0e, '3re', '3 e. RR'), rd1r], '%s e. RR' % RD13), g0r,
                                  D(w, A0e, 'remulcld', [a1(w, A0e, '3re', '3 e. RR'), enb_], '( 3 x. %s ) e. RR' % H), L0_(afz0, '0 <_ ( abs ` ( F ` z ) )'), g00, gb2, G0],
            '( ( abs ` ( F ` z ) ) x. %s ) <_ ( %s x. ( 3 x. %s ) )' % (G0T, RD13, H))
    cl0.leaf(H, 'RR', enb_)
    cl0b = Closure(w, A0e, {DV: ('RR', L0_(dvr, '%s e. RR' % DV)), H: ('RR', enb_), R: ('RR', rr0)})
    m02 = nlinarith(w, A0e, [L0_(gau, '%s <_ 3' % U), L0_(r0z, '0 <_ %s' % R)], '( %s x. ( 3 x. %s ) ) <_ ( ; 3 4 x. %s )' % (RD13, H, R), closure=cl0b)
    e0 = D(w, A0e, 'letrd', [D(w, A0e, 'remulcld', [L0_(afz, '( abs ` ( F ` z ) ) e. RR'), g0r], '( ( abs ` ( F ` z ) ) x. %s ) e. RR' % G0T),
                             D(w, A0e, 'remulcld', [D(w, A0e, 'remulcld', [a1(w, A0e, '3re', '3 e. RR'), rd1r], '%s e. RR' % RD13),
                                                    D(w, A0e, 'remulcld', [a1(w, A0e, '3re', '3 e. RR'), enb_], '( 3 x. %s ) e. RR' % H)], '( %s x. ( 3 x. %s ) ) e. RR' % (RD13, H)),
                             L0_(L(D(w, A, 'rpred', [qqrp], '%s e. RR' % QQ), '%s e. RR' % QQ) if False else w.s([D(w, A, 'rpred', [qqrp], '%s e. RR' % QQ)], 'adantr', '( %s -> %s e. RR )' % (Az, QQ)), '%s e. RR' % QQ),
                             m01, m02], '( ( abs ` ( F ` z ) ) x. %s ) <_ %s' % (G0T, QQ))
    # the power factor at Re = 0: e ^ ( ( 0 - 0 ) log q ) = 1
    z00 = w.s([w.s([w.s([w.s([], '0cn', '0 e. CC')], 'subidi', '( 0 - 0 ) = 0')], 'oveq1i', '( ( 0 - 0 ) x. %s ) = ( 0 x. %s )' % (LQ, LQ))], 'a1i',
              '( %s -> ( ( 0 - 0 ) x. %s ) = ( 0 x. %s ) )' % (A0e, LQ, LQ))
    z01 = D(w, A0e, 'mul02d', [D(w, A0e, 'recnd', [L0_(lqz, '%s e. RR' % LQ)], '%s e. CC' % LQ)], '( 0 x. %s ) = 0' % LQ)
    z02 = w.s([w.s([z00, z01], 'eqtrd', '( %s -> ( ( 0 - 0 ) x. %s ) = 0 )' % (A0e, LQ))], 'fveq2d', '( %s -> ( exp ` ( ( 0 - 0 ) x. %s ) ) = ( exp ` 0 ) )' % (A0e, LQ))
    z03 = w.s([z02, a1(w, A0e, 'ef0', '( exp ` 0 ) = 1')], 'eqtrd', '( %s -> ( exp ` ( ( 0 - 0 ) x. %s ) ) = 1 )' % (A0e, LQ))
    z04 = w.s([z03], 'oveq2d', '( %s -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( 0 - 0 ) x. %s ) ) ) = ( ( ( abs ` ( F ` z ) ) x. %s ) x. 1 ) )' % (A0e, G0T, LQ, G0T))
    z05 = D(w, A0e, 'mulridd', [D(w, A0e, 'recnd', [D(w, A0e, 'remulcld', [L0_(afz, '( abs ` ( F ` z ) ) e. RR'), g0r], '( ( abs ` ( F ` z ) ) x. %s ) e. RR' % G0T)],
                                  '( ( abs ` ( F ` z ) ) x. %s ) e. CC' % G0T)], '( ( ( abs ` ( F ` z ) ) x. %s ) x. 1 ) = ( ( abs ` ( F ` z ) ) x. %s )' % (G0T, G0T))
    e02 = w.s([w.s([z04, z05], 'eqtrd', '( %s -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( 0 - 0 ) x. %s ) ) ) = ( ( abs ` ( F ` z ) ) x. %s ) )' % (A0e, G0T, LQ, G0T)), e0],
              'eqbrtrd', '( %s -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( 0 - 0 ) x. %s ) ) ) <_ %s )' % (A0e, G0T, LQ, QQ))
    ex0 = w.s([e02], 'ex', '( %s -> ( ( Re ` z ) = 0 -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( 0 - 0 ) x. %s ) ) ) <_ %s ) )' % (Az, G0T, LQ, QQ))
    r0 = w.s([ex0], 'ralrimiva', '( %s -> A. z e. %s ( ( Re ` z ) = 0 -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( 0 - 0 ) x. %s ) ) ) <_ %s ) )' % (A, S, G0T, LQ, QQ))
    # zl2pln
    PA = (PLNA.replace('( X e. RR /\\ Y e. RR )', '( -u ( 1 / 2 ) e. RR /\\ 0 e. RR )').replace('( X [,] Y )', '( -u ( 1 / 2 ) [,] 0 )')
          .replace('( P e. RR /\\ C e. RR )', '( 0 e. RR /\\ %s e. RR )' % LQ).replace('Q e. RR+', '%s e. RR+' % QQ))
    PA = PA.replace(PLNL('X').replace('( X [,] Y )', '( -u ( 1 / 2 ) [,] 0 )'), 'LXX').replace(PLNL('Y').replace('( X [,] Y )', '( -u ( 1 / 2 ) [,] 0 )'), 'LYY')
    LXX = w.lines[-1]  # placeholder read below
    LX_ = 'A. z e. %s ( ( Re ` z ) = -u ( 1 / 2 ) -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( -u ( 1 / 2 ) - 0 ) x. %s ) ) ) <_ %s )' % (S, GL, LQ, QQ)
    LY_ = 'A. z e. %s ( ( Re ` z ) = 0 -> ( ( ( abs ` ( F ` z ) ) x. %s ) x. ( exp ` ( ( 0 - 0 ) x. %s ) ) ) <_ %s )' % (S, G0T, LQ, QQ)
    PA = PA.replace('LXX', LX_).replace('LYY', LY_)
    # the growth hypothesis with its quantifier renamed to y (zl2pln is cited at z := y)
    GRB = '( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) )'
    GRY = GRWB('F', S, z='y')
    n0 = len(w.lines)
    idg = w.s([], 'id', '( z = y -> z = y )')
    stg, valg = w.wcongr(GRB, {'z': 'y'}, 'z = y', {'z': idg})
    cbv = w.s([stg], 'cbvralvw', '( A. z e. %s %s <-> A. y e. %s %s )' % (S, GRB, S, valg))
    SKIP.update(range(n0, len(w.lines)))
    gral = D(w, A, 'simprd', [gr], 'A. z e. %s %s' % (S, GRB))
    graly = w.s([gral, cbv], 'sylib', '( %s -> A. y e. %s %s )' % (A, S, valg))
    gry = w.s([D(w, A, 'simpld', [gr], '( K e. RR+ /\\ B e. RR /\\ 0 <_ B )'), graly], 'jca', '( %s -> %s )' % (A, GRY))
    PA = PA.replace(GRWB('F', S), GRY)
    assert GRY in PA
    j1 = w.s([w.s([w.s([nh, z0], 'jca', '( %s -> ( -u ( 1 / 2 ) e. RR /\\ 0 e. RR ) )' % A), hol3], 'jca',
                  '( %s -> ( ( -u ( 1 / 2 ) e. RR /\\ 0 e. RR ) /\\ ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) ) )' % (A, S)), gry], 'jca',
             '( %s -> ( ( ( -u ( 1 / 2 ) e. RR /\\ 0 e. RR ) /\\ ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) ) /\\ %s ) )' % (A, S, GRY))
    j2 = w.s([w.s([ws, w.s([z0, lqr], 'jca', '( %s -> ( 0 e. RR /\\ %s e. RR ) )' % (A, LQ)), qqrp], '3jca',
                  '( %s -> ( W e. %s /\\ ( 0 e. RR /\\ %s e. RR ) /\\ %s e. RR+ ) )' % (A, S, LQ, QQ)), w.s([rL, r0], 'jca', '( %s -> ( %s /\\ %s ) )' % (A, LX_, LY_))], 'jca',
             '( %s -> ( ( W e. %s /\\ ( 0 e. RR /\\ %s e. RR ) /\\ %s e. RR+ ) /\\ ( %s /\\ %s ) ) )' % (A, S, LQ, QQ, LX_, LY_))
    pl = w.s([w.s([j1, j2], 'jca', '( %s -> %s )' % (A, PA)), w.inst('zl2pln')], 'syl',
             '( %s -> ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( Re ` W ) - 0 ) x. %s ) ) ) <_ %s )' % (A, LQ, QQ))
    # e ^ ( ( Re W - 0 ) log q ) = q ^ Re W, and divide
    QW = '( %s ^c ( Re ` W ) )' % Qd
    s1 = D(w, A, 'subid1d', [D(w, A, 'recnd', [wr], '( Re ` W ) e. CC')], '( ( Re ` W ) - 0 ) = ( Re ` W )')
    s2 = E(w, A, 'fveq2d', [E(w, A, 'oveq1d', [s1], '( ( ( Re ` W ) - 0 ) x. %s )' % LQ, '( ( Re ` W ) x. %s )' % LQ)],
           '( exp ` ( ( ( Re ` W ) - 0 ) x. %s ) )' % LQ, '( exp ` ( ( Re ` W ) x. %s ) )' % LQ)
    qcA = D(w, A, 'rpcnd', [qrp], '%s e. CC' % Qd)
    qnA = D(w, A, 'rpne0d', [qrp], '%s =/= 0' % Qd)
    s3 = D(w, A, 'cxpefd', [qcA, qnA, D(w, A, 'recnd', [wr], '( Re ` W ) e. CC')], '%s = ( exp ` ( ( Re ` W ) x. %s ) )' % (QW, LQ))
    s4 = w.s([s2, s3], 'eqtr4d', '( %s -> ( exp ` ( ( ( Re ` W ) - 0 ) x. %s ) ) = %s )' % (A, LQ, QW))
    pl2 = w.s([w.s([s4], 'oveq2d', '( %s -> ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( Re ` W ) - 0 ) x. %s ) ) ) = ( ( abs ` ( F ` W ) ) x. %s ) )' % (A, LQ, QW)), pl],
              'eqbrtrrd', '( %s -> ( ( abs ` ( F ` W ) ) x. %s ) <_ %s )' % (A, QW, QQ))
    qwrp = D(w, A, 'rpcxpcld', [qrp, wr], '%s e. RR+' % QW)
    fwc = w.s([ff, w.s([sd, ws], 'sseldd', '( %s -> W e. D )' % A)], 'ffvelcdmd', '( %s -> ( F ` W ) e. CC )' % A)
    afw = D(w, A, 'abscld', [fwc], '( abs ` ( F ` W ) ) e. RR')
    dv_ = w.s([pl2, D(w, A, 'lemuldivd', [afw, D(w, A, 'rpred', [qqrp], '%s e. RR' % QQ), qwrp], '( ( ( abs ` ( F ` W ) ) x. %s ) <_ %s <-> ( abs ` ( F ` W ) ) <_ ( %s / %s ) )' % (QW, QQ, QQ, QW))],
              'mpbid', '( %s -> ( abs ` ( F ` W ) ) <_ ( %s / %s ) )' % (A, QQ, QW))
    GQW = GQ('W')
    k1 = D(w, A, 'divassd', [a1(w, A, 'id' if False else '4cn', 'x') if False else w.s([w.s([w.s([w.s([], '3nn0', '3 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '; 3 4 e. NN0')], 'nn0cni', '; 3 4 e. CC')], 'a1i', '( %s -> ; 3 4 e. CC )' % A),
                             D(w, A, 'rpcnd', [rrp], '%s e. CC' % R), D(w, A, 'rpcnd', [qwrp], '%s e. CC' % QW), D(w, A, 'rpne0d', [qwrp], '%s =/= 0' % QW)],
           '( %s / %s ) = ( ; 3 4 x. ( %s / %s ) )' % (QQ, QW, R, QW))
    k2 = D(w, A, 'cxpsubd', [qcA, qnA, a1(w, A, 'halfcn', '( 1 / 2 ) e. CC'), D(w, A, 'recnd', [wr], '( Re ` W ) e. CC')], '%s = ( %s / %s )' % (GQW, R, QW))
    k3 = w.s([k1, w.s([w.s([k2], 'eqcomd', '( %s -> ( %s / %s ) = %s )' % (A, R, QW, GQW))], 'oveq2d', '( %s -> ( ; 3 4 x. ( %s / %s ) ) = ( ; 3 4 x. %s ) )' % (A, R, QW, GQW))],
             'eqtrd', '( %s -> ( %s / %s ) = ( ; 3 4 x. %s ) )' % (A, QQ, QW, GQW))
    w.qed([dv_, k3], 'breqtrd', '( %s -> ( abs ` ( F ` W ) ) <_ ( ; 3 4 x. %s ) )' % (A, GQW))
    rename_local(w, ['A. z e. %s %s' % (S, GRB), LM, L0])
    go(w, only)
