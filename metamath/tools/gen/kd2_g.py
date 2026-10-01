"""Sortie KD2: integration (kd2ind, kd2log, kd2am, kd2abel, kd2ibl).  MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_g.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from kd2lib import *
from cl import formula_of, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, nlinarith
from mvlib import ringeq, ringeqp
import num

only = sys.argv[1:]


def hyps(w, label):
    return [w.s([], '%s.%d' % (label, k + 1), f, name='h%d' % (k + 1)) for k, f in enumerate(HYPS[label])]


def gen_ind():
    w = W('kd2ind', 'An indicator integral: for ` Y < A <_ Z ` and ` F ` integrable on ` ( A , Z ) ` , ` u |-> if ( A <_ u , F , 0 ) ` is integrable on ` ( Y , Z ) ` with the same integral ( ~ itgss3 across the null set ` { A } ` , ~ iblss2 , ~ itgss ).')
    A0 = 'ph'
    h1, h2, h3, h4 = hyps(w, 'kd2ind')
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    yr = d('simpld', [h1], 'Y e. RR'); zr = d('simprd', [h1], 'Z e. RR')
    ar = d('simp1d', [h2], 'A e. RR'); ya = d('simp2d', [h2], 'Y < A'); az = d('simp3d', [h2], 'A <_ Z')
    C = 'if ( A <_ u , F , 0 )'
    IO = '( A (,) Z )'; IC = '( A [,) Z )'; YZ = '( Y (,) Z )'
    zx = d('rexrd', [zr], 'Z e. RR*'); yx = d('rexrd', [yr], 'Y e. RR*')
    s1 = a1(w, A0, 'ioossico', '%s C_ %s' % (IO, IC))
    s2 = d('syl2anc', [ar, zx, w.inst('icossre')], '%s C_ RR' % IC)
    # [A,Z) \ (A,Z) C_ { A }
    Au = '( ph /\\ u e. ( %s \\ %s ) )' % (IC, IO)
    du = lambda ref, h, c: D(w, Au, ref, h, c)
    ud = w.s([], 'simpr', '( %s -> u e. ( %s \\ %s ) )' % (Au, IC, IO))
    uic = du('syl', [ud, w.inst('eldifi')], 'u e. %s' % IC); unio = du('syl', [ud, w.inst('eldifn')], '-. u e. %s' % IO)
    g = du('mpbid', [uic, du('syl2anc', [lift(w, ar, Au), lift(w, zx, Au), w.inst('elico2')], '( u e. %s <-> ( u e. RR /\\ A <_ u /\\ u < Z ) )' % IC)], '( u e. RR /\\ A <_ u /\\ u < Z )')
    ur = du('simp1d', [g], 'u e. RR'); au = du('simp2d', [g], 'A <_ u'); uz_ = du('simp3d', [g], 'u < Z')
    Aul = '( %s /\\ A < u )' % Au
    inio = D(w, Aul, 'mpbird', [D(w, Aul, '3jca', [lift(w, ur, Aul), w.s([], 'simpr', '( %s -> A < u )' % Aul), lift(w, uz_, Aul)], '( u e. RR /\\ A < u /\\ u < Z )'),
                                D(w, Aul, 'syl2anc', [D(w, Aul, 'rexrd', [lift(w, ar, Aul)], 'A e. RR*'), lift(w, zx, Aul), w.inst('elioo2')], '( u e. %s <-> ( u e. RR /\\ A < u /\\ u < Z ) )' % IO)],
             'u e. %s' % IO)
    nlt = du('mtod', [unio, w.s([inio], 'ex', '( %s -> ( A < u -> u e. %s ) )' % (Au, IO))], '-. A < u')
    ule = du('mpbird', [nlt, du('lenltd', [ur, lift(w, ar, Au)], '( u <_ A <-> -. A < u )')], 'u <_ A')
    ua = du('letri3d' if False else 'mpbir2and' if False else 'syl3anc' if False else 'letri3d', [ur, lift(w, ar, Au)], '( u = A <-> ( u <_ A /\\ A <_ u ) )')
    ueq = du('mpbird', [du('jca', [ule, au], '( u <_ A /\\ A <_ u )'), ua], 'u = A')
    usn = du('mpbird', [ueq, w.s([], 'velsn', '( u e. { A } <-> u = A )') if False else du('idi', [], 'T.') if False else w.s([w.s([], 'velsn', '( u e. { A } <-> u = A )')], 'a1i', '( %s -> ( u e. { A } <-> u = A ) )' % Au)], 'u e. { A }')
    dsn = d('ssrdv', [w.s([usn], 'ex', '( ph -> ( u e. ( %s \\ %s ) -> u e. { A } ) )' % (IC, IO))], '( %s \\ %s ) C_ { A }' % (IC, IO))
    snr = d('snssd', [ar], '{ A } C_ RR')
    vsn = d('syl', [ar, w.inst('ovolsn')], '( vol* ` { A } ) = 0')
    vnul = d('syl3anc', [dsn, snr, vsn, w.inst('ovolssnul')], '( vol* ` ( %s \\ %s ) ) = 0' % (IC, IO))
    # C e. CC on [A,Z) (on (Y,Z))
    Ay = '( ph /\\ u e. %s )' % YZ
    icsy = d('syl2anc', [d('jca', [yx, zx], '( Y e. RR* /\\ Z e. RR* )'), d('jca', [ya, d('leidd', [zr], 'Z <_ Z')], '( Y < A /\\ Z <_ Z )'), w.inst('icossioo')], '%s C_ %s' % (IC, YZ))
    Aic = '( ph /\\ u e. %s )' % IC
    uyz = D(w, Aic, 'sseldd', [lift(w, icsy, Aic), w.s([], 'simpr', '( %s -> u e. %s )' % (Aic, IC))], 'u e. %s' % YZ)
    h4ex = w.s([h4], 'ex', '( ph -> ( u e. %s -> F e. CC ) )' % YZ)
    fic = D(w, Aic, 'mpd', [uyz, lift(w, h4ex, Aic)], 'F e. CC')
    cic = D(w, Aic, 'ifcld', [fic, a1(w, Aic, '0cn', '0 e. CC')], '%s e. CC' % C)
    i3 = d('itgss3', [s1, s2, vnul, cic], '( ( ( u e. %s |-> %s ) e. L^1 <-> ( u e. %s |-> %s ) e. L^1 ) /\\ S. %s %s _d u = S. %s %s _d u )' % (IO, C, IC, C, IO, C, IC, C))
    # on (A,Z): C = F
    Aio = '( ph /\\ u e. %s )' % IO
    uio = w.s([], 'simpr', '( %s -> u e. %s )' % (Aio, IO))
    gio = D(w, Aio, 'mpbid', [uio, D(w, Aio, 'syl2anc', [D(w, Aio, 'rexrd', [lift(w, ar, Aio)], 'A e. RR*'), lift(w, zx, Aio), w.inst('elioo2')], '( u e. %s <-> ( u e. RR /\\ A < u /\\ u < Z ) )' % IO)],
              '( u e. RR /\\ A < u /\\ u < Z )')
    aule = D(w, Aio, 'ltled', [lift(w, ar, Aio), D(w, Aio, 'simp1d', [gio], 'u e. RR'), D(w, Aio, 'simp2d', [gio], 'A < u')], 'A <_ u')
    cf = D(w, Aio, 'syl', [aule, w.inst('iftrue')], '%s = F' % C)
    mio = d('mpteq2dva', [cf], '( u e. %s |-> %s ) = ( u e. %s |-> F )' % (IO, C, IO))
    ib1 = d('eqeltrd', [mio, h3], '( u e. %s |-> %s ) e. L^1' % (IO, C))
    ib2 = d('mpbid', [ib1, d('simpld', [i3], '( ( u e. %s |-> %s ) e. L^1 <-> ( u e. %s |-> %s ) e. L^1 )' % (IO, C, IC, C))], '( u e. %s |-> %s ) e. L^1' % (IC, C))
    # extend by zero to (Y,Z)
    Ad = '( ph /\\ u e. ( %s \\ %s ) )' % (YZ, IC)
    udd = w.s([], 'simpr', '( %s -> u e. ( %s \\ %s ) )' % (Ad, YZ, IC))
    uyz2 = D(w, Ad, 'syl', [udd, w.inst('eldifi')], 'u e. %s' % YZ); unic = D(w, Ad, 'syl', [udd, w.inst('eldifn')], '-. u e. %s' % IC)
    gyz = D(w, Ad, 'mpbid', [uyz2, D(w, Ad, 'syl2anc', [lift(w, yx, Ad), lift(w, zx, Ad), w.inst('elioo2')], '( u e. %s <-> ( u e. RR /\\ Y < u /\\ u < Z ) )' % YZ)], '( u e. RR /\\ Y < u /\\ u < Z )')
    Adl = '( %s /\\ A <_ u )' % Ad
    inic = D(w, Adl, 'mpbird', [D(w, Adl, '3jca', [lift(w, D(w, Ad, 'simp1d', [gyz], 'u e. RR'), Adl), w.s([], 'simpr', '( %s -> A <_ u )' % Adl), lift(w, D(w, Ad, 'simp3d', [gyz], 'u < Z'), Adl)],
                                    '( u e. RR /\\ A <_ u /\\ u < Z )'),
                                D(w, Adl, 'syl2anc', [lift(w, ar, Adl), lift(w, zx, Adl), w.inst('elico2')], '( u e. %s <-> ( u e. RR /\\ A <_ u /\\ u < Z ) )' % IC)], 'u e. %s' % IC)
    nau = D(w, Ad, 'mtod', [unic, w.s([inic], 'ex', '( %s -> ( A <_ u -> u e. %s ) )' % (Ad, IC))], '-. A <_ u')
    c0 = D(w, Ad, 'syl', [nau, w.inst('iffalse')], '%s = 0' % C)
    ib3 = d('iblss2', [icsy, a1(w, A0, 'ioombl', '%s e. dom vol' % YZ), cic, c0, ib2], '( u e. %s |-> %s ) e. L^1' % (YZ, C))
    it1 = d('itgss', [icsy, c0], 'S. %s %s _d u = S. %s %s _d u' % (IC, C, YZ, C))
    it0 = d('itgeq2dv', [cf], 'S. %s %s _d u = S. %s F _d u' % (IO, C, IO))
    it2 = d('simprd', [i3], 'S. %s %s _d u = S. %s %s _d u' % (IO, C, IC, C))
    itt = chain(w, A0, ['S. %s %s _d u' % (YZ, C), 'S. %s %s _d u' % (IC, C), 'S. %s %s _d u' % (IO, C), 'S. %s F _d u' % IO], [('r', it1), ('r', it2), it0])
    fin = d('jca', [ib3, itt], S['kd2ind'].split(' -> ', 1)[1][:-2])
    w.qed([fin], 'idi', S['kd2ind'])
    return only_run(w, only)


def rpsets(w, A, ap, br):
    """( A -> ( P [,] Q ) C_ RR+ ) and ( A -> ( P (,) Q ) C_ RR+ ) for ap : ( A -> P e. RR+ ), br : ( A -> Q e. RR )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    P = formula_of(w, ap).split(' -> ')[1].split(' e. ')[0]; Q = formula_of(w, br).split(' -> ')[1].split(' e. ')[0]
    ic = d('syl2anc', [d('jca', [a1(w, A, '0xr', '0 e. RR*'), a1(w, A, 'pnfxr', '+oo e. RR*')], '( 0 e. RR* /\\ +oo e. RR* )'),
                       d('jca', [d('rpgt0d', [ap], '0 < %s' % P), d('ltpnfd', [br], '%s < +oo' % Q)], '( 0 < %s /\\ %s < +oo )' % (P, Q)), w.inst('iccssioo')], '( %s [,] %s ) C_ ( 0 (,) +oo )' % (P, Q))
    icr = d('sseqtrd', [ic, a1(w, A, 'ioorp', '( 0 (,) +oo ) = RR+')], '( %s [,] %s ) C_ RR+' % (P, Q))
    ior = d('sstrd', [a1(w, A, 'ioossicc', '( %s (,) %s ) C_ ( %s [,] %s )' % (P, Q, P, Q)), icr], '( %s (,) %s ) C_ RR+' % (P, Q))
    return icr, ior


def restr(w, A, cst, X, B):
    """( A -> ( u e. X |-> B ) e. ( X -cn-> CC ) ) from cst : ( A -> ( u e. RR+ |-> B ) e. ( RR+ -cn-> CC ) ) and xs : X C_ RR+ (passed as tuple)"""
    X_, xs = X
    d = lambda ref, h, c: D(w, A, ref, h, c)
    r = d('mpd', [cst, d('syl', [xs, w.inst('rescncf')], '( ( u e. RR+ |-> %s ) e. ( RR+ -cn-> CC ) -> ( ( u e. RR+ |-> %s ) |` %s ) e. ( %s -cn-> CC ) )' % (B, B, X_, X_))],
          '( ( u e. RR+ |-> %s ) |` %s ) e. ( %s -cn-> CC )' % (B, X_, X_))
    e = d('syl', [xs, w.inst('resmpt')], '( ( u e. RR+ |-> %s ) |` %s ) = ( u e. %s |-> %s )' % (B, X_, X_, B))
    return d('eqeltrrd', [e, r], '( u e. %s |-> %s ) e. ( %s -cn-> CC )' % (X_, B, X_))


def gen_log():
    w = W('kd2log', 'The logarithmic integral ` S. ( A , B ) 1 / u = log B - log A ` on ` 0 < A <_ B ` , with integrability ( EF1 ~ ef1ftc , ~ dvrelog ).')
    from kd2_f import logmap, contdv
    from zl3d_g import open_ioo
    A0 = S['kd2log'].split(' -> ( ( u e.')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    ap = d('simp1', [], 'A e. RR+'); br = d('simp2', [], 'B e. RR'); ab = d('simp3', [], 'A <_ B')
    ar = d('rpred', [ap], 'A e. RR')
    icr, ior = rpsets(w, A0, ap, br)
    dl = logmap(w, A0)
    Au = '( %s /\\ u e. RR+ )' % A0
    up = w.s([], 'simpr', '( %s -> u e. RR+ )' % Au)
    lgc = D(w, Au, 'recnd', [D(w, Au, 'relogcld', [up], '( log ` u ) e. RR')], '( log ` u ) e. CC')
    iuc = D(w, Au, 'reccld', [D(w, Au, 'rpcnd', [up], 'u e. CC'), D(w, Au, 'rpne0d', [up], 'u =/= 0')], '( 1 / u ) e. CC')
    lcont = contdv(w, A0, '( log ` u )', dl, iuc, lgc)
    dres = d('dvmptres', [a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }'), lgc, iuc, dl, ior, w.s([], 'eqid', '( ( TopOpen ` CCfld ) |`t RR ) = ( ( TopOpen ` CCfld ) |`t RR )'),
                          w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )'), open_ioo(w, A0, 'A', 'B')],
             '( RR _D ( u e. ( A (,) B ) |-> ( log ` u ) ) ) = ( u e. ( A (,) B ) |-> ( 1 / u ) )')
    gc = restr(w, A0, lcont, ('( A [,] B )', icr), '( log ` u )')
    ncz = "( CC \\ { 0 } )"
    Ai = '( %s /\\ u e. ( A [,] B ) )' % A0
    uin = D(w, Ai, 'mpbird' if False else 'sseldd', [lift(w, icr, Ai), w.s([], 'simpr', '( %s -> u e. ( A [,] B ) )' % Ai)], 'u e. RR+')
    iss = d('ssrdv', [w.s([D(w, Ai, 'syl', [uin, w.inst('rpcndif0')], 'u e. %s' % ncz)], 'ex', '( %s -> ( u e. ( A [,] B ) -> u e. %s ) )' % (A0, ncz))], '( A [,] B ) C_ %s' % ncz)
    idc = d('syl', [d('jca', [iss, a1(w, A0, 'difss', '%s C_ CC' % ncz)], '( ( A [,] B ) C_ %s /\\ %s C_ CC )' % (ncz, ncz)), w.inst('cncfmptid')], '( u e. ( A [,] B ) |-> u ) e. ( ( A [,] B ) -cn-> %s )' % ncz)
    icb = d('sstrd', [icr, d('sstrd', [a1(w, A0, 'rpssre', 'RR+ C_ RR'), a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'RR+ C_ CC')], '( A [,] B ) C_ CC')
    one = d('syl', [d('3jca', [a1(w, A0, 'ax-1cn', '1 e. CC'), icb, d('ssidd', [], 'CC C_ CC')], '( 1 e. CC /\\ ( A [,] B ) C_ CC /\\ CC C_ CC )'), w.inst('cncfmptc')], '( u e. ( A [,] B ) |-> 1 ) e. ( ( A [,] B ) -cn-> CC )')
    hc = d('divcncf', [one, idc], '( u e. ( A [,] B ) |-> ( 1 / u ) ) e. ( ( A [,] B ) -cn-> CC )')
    e5 = w.s([], 'fveq2', '( u = A -> ( log ` u ) = ( log ` A ) )'); e6 = w.s([], 'fveq2', '( u = B -> ( log ` u ) = ( log ` B ) )')
    fin = d('ef1ftc', [d('3jca', [ar, br, ab], '( A e. RR /\\ B e. RR /\\ A <_ B )'), gc, dres, hc, e5, e6], S['kd2log'].split(' -> ', 1)[1][:-2])
    w.qed([fin], 'idi', S['kd2log'])
    return only_run(w, only)


def gen_amx():
    w = W('kd2amx', 'Algebra of the endgame: ` 2 G K ( G C ) <_ C ( K^2 I + G^2 K ) ` gives ` G^2 / K <_ I ` .')
    A0 = S['kd2amx'].split(' -> ( ( G ^ 2 )')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simpl', [], '( G e. RR+ /\\ K e. RR+ /\\ C e. RR+ )'); g2 = d('simpr', [], '( I e. RR /\\ ( ( ( 2 x. G ) x. K ) x. ( G x. C ) ) <_ ( C x. ( ( ( K ^ 2 ) x. I ) + ( ( G ^ 2 ) x. K ) ) ) )')
    gp = d('simp1d', [g1], 'G e. RR+'); kp = d('simp2d', [g1], 'K e. RR+'); cp = d('simp3d', [g1], 'C e. RR+')
    ir = d('simpld', [g2], 'I e. RR'); h = d('simprd', [g2], '( ( ( 2 x. G ) x. K ) x. ( G x. C ) ) <_ ( C x. ( ( ( K ^ 2 ) x. I ) + ( ( G ^ 2 ) x. K ) ) )')
    cl = Closure(w, A0, {'G': ('RR+', gp), 'K': ('RR+', kp), 'C': ('RR+', cp), 'I': ('RR', ir)})
    KC = '( K x. C )'
    tD = nlinarith(w, A0, [h], '( %s x. ( G ^ 2 ) ) <_ ( %s x. ( K x. I ) )' % (KC, KC), closure=cl)
    tE = d('mpbird', [tD, d('lemul2d', [cl.mem('( G ^ 2 )', 'RR'), cl.mem('( K x. I )', 'RR'), cl.mem(KC, 'RR+')], '( ( G ^ 2 ) <_ ( K x. I ) <-> ( %s x. ( G ^ 2 ) ) <_ ( %s x. ( K x. I ) ) )' % (KC, KC))],
            '( G ^ 2 ) <_ ( K x. I )')
    tF = d('mpbird', [d('breqtrd', [tE, d('mulcomd', [cl.mem('K', 'CC'), cl.mem('I', 'CC')], '( K x. I ) = ( I x. K )')], '( G ^ 2 ) <_ ( I x. K )'),
                      d('ledivmul2d', [cl.mem('( G ^ 2 )', 'RR'), ir, kp], '( ( ( G ^ 2 ) / K ) <_ I <-> ( G ^ 2 ) <_ ( I x. K ) )')], '( ( G ^ 2 ) / K ) <_ I')
    w.qed([tF], 'idi', S['kd2amx'])
    return only_run(w, only)


def gen_am():
    w = W('kd2am', 'Lean ` KDerivDetect.integral_normSq_div_ge ` (section 4.4 step 5): with ` abs psi ( u ) u <_ C ` and ` G C <_ abs S. psi S ` , ` G^2 / K <_ S. abs S^2 / u ` for any ` K >_ log ( X2 / X1 ) ` ; AM-GM ` 2 G K abs S <_ K^2 abs S^2 + G^2 ` pointwise.')
    A0 = 'ph'
    h1, h2, h3, h4, h5, h6 = hyps(w, 'kd2am')
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    yp = d('simp1d', [h1], 'Y e. RR+'); zr = d('simp2d', [h1], 'Z e. RR'); yz = d('simp3d', [h1], 'Y <_ Z')
    cp = d('simp1d', [h6], 'C e. RR+'); kk = d('simp2d', [h6], '( K e. RR+ /\\ ( ( log ` Z ) - ( log ` Y ) ) <_ K )'); gg = d('simp3d', [h6], '( G e. RR+ /\\ ( G x. C ) <_ ( abs ` S. ( Y (,) Z ) ( P x. F ) _d u ) )')
    kp = d('simpld', [kk], 'K e. RR+'); lk = d('simprd', [kk], '( ( log ` Z ) - ( log ` Y ) ) <_ K')
    gp = d('simpld', [gg], 'G e. RR+'); gc = d('simprd', [gg], '( G x. C ) <_ ( abs ` S. ( Y (,) Z ) ( P x. F ) _d u )')
    YZ = '( Y (,) Z )'
    lg = use(w, A0, 'kd2log', {'A': 'Y', 'B': 'Z'}, d('3jca', [yp, zr, yz], '( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z )'))
    ib1u = d('simpld', [lg], '( u e. %s |-> ( 1 / u ) ) e. L^1' % YZ); it1u = d('simprd', [lg], 'S. %s ( 1 / u ) _d u = ( ( log ` Z ) - ( log ` Y ) )' % YZ)
    Au = '( ph /\\ u e. %s )' % YZ
    du = lambda ref, h, c: D(w, Au, ref, h, c)
    L = lambda st: lift(w, st, Au)
    uio = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, YZ))
    ur = du('syl', [uio, w.inst('elioore')], 'u e. RR')
    yu = du('simpld', [du('syl', [uio, w.inst('eliooord')], '( Y < u /\\ u < Z )')], 'Y < u')
    upp = du('elrpd', [ur, du('lttrd' if False else 'ltletrd' if False else 'lelttrd', [a1(w, Au, '0re', '0 e. RR'), du('rpred', [L(yp)], 'Y e. RR'), ur, du('rpge0d', [L(yp)], '0 <_ Y'), yu], '0 < u')], 'u e. RR+')
    pf = h4
    pr_ = du('simpld', [pf], 'P e. RR'); fc = du('simprd', [pf], 'F e. CC')
    AF = '( abs ` F )'; AP = '( abs ` P )'
    afr = du('abscld', [fc], '%s e. RR' % AF); af0 = du('absge0d', [fc], '0 <_ %s' % AF)
    apr = du('abscld', [du('recnd', [pr_], 'P e. CC')], '%s e. RR' % AP); ap0 = du('absge0d', [du('recnd', [pr_], 'P e. CC')], '0 <_ %s' % AP)
    Cr = L(d('rpred', [cp], 'C e. RR')); Kr = L(d('rpred', [kp], 'K e. RR')); Gr = L(d('rpred', [gp], 'G e. RR'))
    # |P| <_ C / u
    ple = du('mpbid', [h5, du('lemuldivd', [apr, Cr, upp], '( ( %s x. u ) <_ C <-> %s <_ ( C / u ) )' % (AP, AP))], '%s <_ ( C / u )' % AP)
    # 2 G K |F| <_ K^2 |F|^2 + G^2
    clq = Closure(w, Au, {AF: ('RR', afr), 'K': ('RR+', L(kp)), 'G': ('RR+', L(gp))}); clq.atom(AF)
    sq = du('sqge0d', [clq.mem('( ( K x. %s ) - G )' % AF, 'RR')], '0 <_ ( ( ( K x. %s ) - G ) ^ 2 )' % AF)
    from mvlib import ringeqp
    amg = nlinarith(w, Au, [sq], '( ( ( 2 x. G ) x. K ) x. %s ) <_ ( ( ( K ^ 2 ) x. ( %s ^ 2 ) ) + ( G ^ 2 ) )' % (AF, AF), closure=clq)
    TGK = '( ( 2 x. G ) x. K )'
    X2 = '( ( ( K ^ 2 ) x. ( %s ^ 2 ) ) + ( G ^ 2 ) )' % AF
    x0 = du('mulge0d', [clq.mem(TGK, 'RR'), afr, clq.ge0(TGK), af0], '0 <_ ( %s x. %s )' % (TGK, AF))
    p1 = du('lemul12ad', [apr, du('rerpdivcld', [Cr, upp], '( C / u ) e. RR'), clq.mem('( %s x. %s )' % (TGK, AF), 'RR'), clq.mem(X2, 'RR'), ap0, x0, ple, amg],
            '( %s x. ( %s x. %s ) ) <_ ( ( C / u ) x. %s )' % (AP, TGK, AF, X2))
    PF = '( P x. F )'
    apf = du('absmuld', [du('recnd', [pr_], 'P e. CC'), fc], '( abs ` %s ) = ( %s x. %s )' % (PF, AP, AF))
    IU = '( 1 / u )'
    iuc = du('reccld', [du('rpcnd', [upp], 'u e. CC'), du('rpne0d', [upp], 'u =/= 0')], '%s e. CC' % IU)
    c1 = du('divrecd', [du('recnd', [Cr], 'C e. CC'), du('rpcnd', [upp], 'u e. CC'), du('rpne0d', [upp], 'u =/= 0')], '( C / u ) = ( C x. %s )' % IU)
    Q2 = '( ( %s ^ 2 ) / u )' % AF
    c2 = du('divrecd', [du('recnd', [du('resqcld', [afr], '( %s ^ 2 ) e. RR' % AF)], '( %s ^ 2 ) e. CC' % AF), du('rpcnd', [upp], 'u e. CC'), du('rpne0d', [upp], 'u =/= 0')], '%s = ( ( %s ^ 2 ) x. %s )' % (Q2, AF, IU))
    F1 = '( %s x. ( abs ` %s ) )' % (TGK, PF)
    F2 = '( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) ) )' % (Q2, IU)
    clr = Closure(w, Au, {AF: ('CC', du('recnd', [afr], '%s e. CC' % AF)), AP: ('CC', du('recnd', [apr], '%s e. CC' % AP)), IU: ('CC', iuc), 'C': ('CC', du('recnd', [Cr], 'C e. CC')),
                          'K': ('CC', du('recnd', [Kr], 'K e. CC')), 'G': ('CC', du('recnd', [Gr], 'G e. CC'))})
    for a in (AF, AP, IU):
        clr.atom(a)
    e1 = du('eqtrd', [du('oveq2d', [apf], '%s = ( %s x. ( %s x. %s ) )' % (F1, TGK, AP, AF)), ringeq(w, Au, '( %s x. ( %s x. %s ) )' % (TGK, AP, AF), '( %s x. ( %s x. %s ) )' % (AP, TGK, AF), clr)],
            '%s = ( %s x. ( %s x. %s ) )' % (F1, AP, TGK, AF))
    e2 = du('eqtrd', [du('oveq1d', [c1], '( ( C / u ) x. %s ) = ( ( C x. %s ) x. %s )' % (X2, IU, X2)),
                      du('eqtr4d', [ringeq(w, Au, '( ( C x. %s ) x. %s )' % (IU, X2), '( C x. ( ( ( K ^ 2 ) x. ( ( %s ^ 2 ) x. %s ) ) + ( ( G ^ 2 ) x. %s ) ) )' % (AF, IU, IU), clr),
                                    du('oveq2d', [du('oveq1d', [du('oveq2d', [c2], '( ( K ^ 2 ) x. %s ) = ( ( K ^ 2 ) x. ( ( %s ^ 2 ) x. %s ) )' % (Q2, AF, IU))],
                                                                '( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) ) = ( ( ( K ^ 2 ) x. ( ( %s ^ 2 ) x. %s ) ) + ( ( G ^ 2 ) x. %s ) )' % (Q2, IU, AF, IU, IU))],
                                       '%s = ( C x. ( ( ( K ^ 2 ) x. ( ( %s ^ 2 ) x. %s ) ) + ( ( G ^ 2 ) x. %s ) ) )' % (F2, AF, IU, IU))],
                         '( ( C x. %s ) x. %s ) = %s' % (IU, X2, F2))], '( ( C / u ) x. %s ) = %s' % (X2, F2))
    pw = du('breqtrd', [du('eqbrtrd', [e1, p1], '%s <_ ( ( C / u ) x. %s )' % (F1, X2)), e2], '%s <_ %s' % (F1, F2))
    # integrability and integrals
    pfc = du('mulcld', [du('recnd', [pr_], 'P e. CC'), fc], '%s e. CC' % PF)
    ib_abs = d('iblabs', [pfc, h2], '( u e. %s |-> ( abs ` %s ) ) e. L^1' % (YZ, PF))
    tgkc = d('recnd', [Closure(w, A0, {'G': ('RR+', gp), 'K': ('RR+', kp)}).mem(TGK, 'RR')], '%s e. CC' % TGK)
    apfr = du('abscld', [pfc], '( abs ` %s ) e. RR' % PF)
    ibF1 = d('iblmulc2', [tgkc, du('recnd', [apfr], '( abs ` %s ) e. CC' % PF), ib_abs], '( u e. %s |-> %s ) e. L^1' % (YZ, F1))
    q2c = du('recnd', [du('rerpdivcld', [du('resqcld', [afr], '( %s ^ 2 ) e. RR' % AF), upp], '%s e. RR' % Q2)], '%s e. CC' % Q2)
    k2c = d('recnd', [d('resqcld', [d('rpred', [kp], 'K e. RR')], '( K ^ 2 ) e. RR')], '( K ^ 2 ) e. CC')
    g2c = d('recnd', [d('resqcld', [d('rpred', [gp], 'G e. RR')], '( G ^ 2 ) e. RR')], '( G ^ 2 ) e. CC')
    A1_ = '( ( K ^ 2 ) x. %s )' % Q2; A2_ = '( ( G ^ 2 ) x. %s )' % IU
    iA1 = d('iblmulc2', [k2c, q2c, h3], '( u e. %s |-> %s ) e. L^1' % (YZ, A1_))
    iA2 = d('iblmulc2', [g2c, iuc, ib1u], '( u e. %s |-> %s ) e. L^1' % (YZ, A2_))
    a1c = du('mulcld', [L(k2c), q2c], '%s e. CC' % A1_); a2c = du('mulcld', [L(g2c), iuc], '%s e. CC' % A2_)
    iS = d('ibladd', [a1c, iA1, a2c, iA2], '( u e. %s |-> ( %s + %s ) ) e. L^1' % (YZ, A1_, A2_))
    sc = du('addcld', [a1c, a2c], '( %s + %s ) e. CC' % (A1_, A2_))
    ibF2 = d('iblmulc2', [d('recnd', [d('rpred', [cp], 'C e. RR')], 'C e. CC'), sc, iS], '( u e. %s |-> %s ) e. L^1' % (YZ, F2))
    f1r = du('remulcld', [du('recnd' if False else 'remulcld', [du('remulcld', [a1(w, Au, '2re', '2 e. RR'), Gr], '( 2 x. G ) e. RR'), Kr], '%s e. RR' % TGK), apfr], '%s e. RR' % F1)
    f2r = du('remulcld', [Cr, du('readdcld', [du('remulcld', [du('resqcld', [Kr], '( K ^ 2 ) e. RR'), du('rerpdivcld', [du('resqcld', [afr], '( %s ^ 2 ) e. RR' % AF), upp], '%s e. RR' % Q2)], '%s e. RR' % A1_),
                                                  du('remulcld', [du('resqcld', [Gr], '( G ^ 2 ) e. RR'), du('rpreccld', [upp], '%s e. RR+' % IU) if False else du('rerpdivcld', [a1(w, Au, '1re', '1 e. RR'), upp], '%s e. RR' % IU)], '%s e. RR' % A2_)],
                                     '( %s + %s ) e. RR' % (A1_, A2_))], '%s e. RR' % F2)
    ile = d('itgle', [ibF1, ibF2, f1r, f2r, pw], 'S. %s %s _d u <_ S. %s %s _d u' % (YZ, F1, YZ, F2))
    J2 = 'S. %s ( abs ` %s ) _d u' % (YZ, PF)
    m1 = d('itgmulc2', [tgkc, du('recnd', [apfr], '( abs ` %s ) e. CC' % PF), ib_abs], '( %s x. %s ) = S. %s %s _d u' % (TGK, J2, YZ, F1))
    I_ = 'S. %s %s _d u' % (YZ, Q2)
    m2 = d('itgmulc2', [d('recnd', [d('rpred', [cp], 'C e. RR')], 'C e. CC'), sc, iS], '( C x. S. %s ( %s + %s ) _d u ) = S. %s %s _d u' % (YZ, A1_, A2_, YZ, F2))
    m3 = d('itgadd', [a1c, iA1, a2c, iA2], 'S. %s ( %s + %s ) _d u = ( S. %s %s _d u + S. %s %s _d u )' % (YZ, A1_, A2_, YZ, A1_, YZ, A2_))
    m4 = d('itgmulc2', [k2c, q2c, h3], '( ( K ^ 2 ) x. %s ) = S. %s %s _d u' % (I_, YZ, A1_))
    m5 = d('itgmulc2', [g2c, iuc, ib1u], '( ( G ^ 2 ) x. S. %s %s _d u ) = S. %s %s _d u' % (YZ, IU, YZ, A2_))
    LL = '( ( log ` Z ) - ( log ` Y ) )'
    m6 = d('oveq2d', [it1u], '( ( G ^ 2 ) x. S. %s %s _d u ) = ( ( G ^ 2 ) x. %s )' % (YZ, IU, LL))
    # S. F2 = C ( K^2 I + G^2 L )
    RS = '( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) ) )' % (I_, LL)
    s2e = d('eqtr3d', [m2, d('oveq2d', [d('eqtrd', [m3, d('oveq12d', [('x', m4), ('x', m5)] if False else [d('eqcomd', [m4], 'S. %s %s _d u = ( ( K ^ 2 ) x. %s )' % (YZ, A1_, I_)),
                                                                                                          d('eqtr3d', [m5, m6], 'S. %s %s _d u = ( ( G ^ 2 ) x. %s )' % (YZ, A2_, LL))],
                                                                     '( S. %s %s _d u + S. %s %s _d u ) = ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) )' % (YZ, A1_, YZ, A2_, I_, LL))],
                                                   'S. %s ( %s + %s ) _d u = ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) )' % (YZ, A1_, A2_, I_, LL))],
                                    '( C x. S. %s ( %s + %s ) _d u ) = %s' % (YZ, A1_, A2_, RS))], 'S. %s %s _d u = %s' % (YZ, F2, RS))
    k1 = d('breqtrd', [d('eqbrtrd', [m1, ile], '( %s x. %s ) <_ S. %s %s _d u' % (TGK, J2, YZ, F2)), s2e], '( %s x. %s ) <_ %s' % (TGK, J2, RS))
    J1 = '( abs ` S. %s %s _d u )' % (YZ, PF)
    k2 = d('itgabs', [pfc, h2], '%s <_ %s' % (J1, J2))
    # final arithmetic: G^2 <_ K I
    ir = d('itgrecl' if False else 'idi', [], 'T.') if False else None
    Aq = '( ph /\\ u e. %s )' % YZ
    q2r = du('rerpdivcld', [du('resqcld', [afr], '( %s ^ 2 ) e. RR' % AF), upp], '%s e. RR' % Q2)
    irr = d('itgrecl', [q2r, h3], '%s e. RR' % I_)
    j2r = d('itgrecl', [apfr, ib_abs], '%s e. RR' % J2)
    j1r = d('abscld', [d('itgcl', [pfc, h2], 'S. %s %s _d u e. CC' % (YZ, PF))], '%s e. RR' % J1)
    llr = d('resubcld', [d('relogcld', [d('elrpd', [zr, d('lelttrd' if False else 'ltletrd', [a1(w, A0, '0re', '0 e. RR'), d('rpred', [yp], 'Y e. RR'), zr, d('rpgt0d', [yp], '0 < Y'), yz], '0 < Z')], 'Z e. RR+')], '( log ` Z ) e. RR'),
                         d('relogcld', [yp], '( log ` Y ) e. RR')], '%s e. RR' % LL)
    cl0 = Closure(w, A0, {'G': ('RR+', gp), 'K': ('RR+', kp), 'C': ('RR+', cp), I_: ('RR', irr), J2: ('RR', j2r), J1: ('RR', j1r), LL: ('RR', llr)})
    for a in (I_, J2, J1, LL):
        cl0.atom(a)
    # 2GK ( G C ) <_ 2GK J1 <_ 2GK J2 <_ RS <_ C ( K^2 I + G^2 K )
    t1 = d('lemul2ad', [cl0.mem('( G x. C )', 'RR'), j1r, cl0.mem(TGK, 'RR'), cl0.ge0(TGK), gc], '( %s x. ( G x. C ) ) <_ ( %s x. %s )' % (TGK, TGK, J1))
    t2 = d('lemul2ad', [j1r, j2r, cl0.mem(TGK, 'RR'), cl0.ge0(TGK), k2], '( %s x. %s ) <_ ( %s x. %s )' % (TGK, J1, TGK, J2))
    t3 = d('lemul2ad', [llr, cl0.mem('K', 'RR'), cl0.mem('( G ^ 2 )', 'RR'), cl0.ge0('( G ^ 2 )'), lk], '( ( G ^ 2 ) x. %s ) <_ ( ( G ^ 2 ) x. K )' % LL)
    t4 = d('lemul2ad', [cl0.mem('( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) )' % (I_, LL), 'RR'), cl0.mem('( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) )' % I_, 'RR'), cl0.mem('C', 'RR'), cl0.ge0('C'),
                        linarith(w, A0, [t3], '( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. %s ) ) <_ ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) )' % (I_, LL, I_), closure=cl0)],
            '%s <_ ( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) ) )' % (RS, I_))
    tA = d('letrd', [cl0.mem('( %s x. ( G x. C ) )' % TGK, 'RR'), cl0.mem('( %s x. %s )' % (TGK, J1), 'RR'), cl0.mem('( %s x. %s )' % (TGK, J2), 'RR'), t1, t2], '( %s x. ( G x. C ) ) <_ ( %s x. %s )' % (TGK, TGK, J2))
    tB = d('letrd', [cl0.mem('( %s x. ( G x. C ) )' % TGK, 'RR'), cl0.mem('( %s x. %s )' % (TGK, J2), 'RR'), cl0.mem(RS, 'RR'), tA, k1], '( %s x. ( G x. C ) ) <_ %s' % (TGK, RS))
    tC = d('letrd', [cl0.mem('( %s x. ( G x. C ) )' % TGK, 'RR'), cl0.mem(RS, 'RR'), cl0.mem('( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) ) )' % I_, 'RR'), tB, t4],
           '( %s x. ( G x. C ) ) <_ ( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) ) )' % (TGK, I_))
    tF = use(w, A0, 'kd2amx', {'I': I_}, d('jca', [d('3jca', [gp, kp, cp], '( G e. RR+ /\\ K e. RR+ /\\ C e. RR+ )'), d('jca', [irr, tC], '( %s e. RR /\\ ( %s x. ( G x. C ) ) <_ ( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) ) ) )' % (I_, TGK, I_))],
                                                 '( ( G e. RR+ /\\ K e. RR+ /\\ C e. RR+ ) /\\ ( %s e. RR /\\ ( %s x. ( G x. C ) ) <_ ( C x. ( ( ( K ^ 2 ) x. %s ) + ( ( G ^ 2 ) x. K ) ) ) ) )' % (I_, TGK, I_)))
    w.qed([tF], 'idi', S['kd2am'])
    return only_run(w, only)


def gen_abel():
    w = W('kd2abel', 'Lean ` KDerivDetect.abel_window ` : ` Dwin = phi ( X2 ) S ( X2 ) - S. ( X1 , X2 ) psi ( u ) S ( u ) ` with integrability, by the FTC per prime ( EF1 ~ ef1ftc with ~ kd2dv ), the indicator integral ~ kd2ind and ~ itgfsum over the window ( ~ kd2pwsif ).')
    from kd2_f import contdv
    from kd2_e import psmem, cpcc
    from zl3d_g import open_ioo
    A0 = S['kd2abel'].split(' -> ( ( u e.')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    nxh = d('simp1', [], NXH); g2 = d('simp2', [], '( T e. RR /\\ E e. RR /\\ J e. NN0 )'); g3 = d('simp3', [], '( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z )')
    tr = d('simp1d', [g2], 'T e. RR'); er = d('simp2d', [g2], 'E e. RR'); jn = d('simp3d', [g2], 'J e. NN0')
    yp = d('simp1d', [g3], 'Y e. RR+'); zr = d('simp2d', [g3], 'Z e. RR'); yz = d('simp3d', [g3], 'Y <_ Z')
    yr = d('rpred', [yp], 'Y e. RR')
    YZ = '( Y (,) Z )'; PZ = PSET('Y', 'Z')
    PHu, PSu = PHI('J', 'u'), PSI('J', 'u')
    dv = use(w, A0, 'kd2dv', {}, d('jca', [er, jn], '( E e. RR /\\ J e. NN0 )'))
    dvf = d('simpld', [dv], '( RR _D ( u e. RR+ |-> %s ) ) = ( u e. RR+ |-> %s )' % (PHu, PSu))
    psc = d('simprd', [dv], '( u e. RR+ |-> %s ) e. ( RR+ -cn-> CC )' % PSu)
    Ar = '( %s /\\ u e. RR+ )' % A0
    upr = w.s([], 'simpr', '( %s -> u e. RR+ )' % Ar)
    def phc_(Ah, up):
        dd = lambda ref, h, c: D(w, Ah, ref, h, c)
        return dd('mulcld', [dd('expcld', [dd('recnd', [dd('relogcld', [up], '( log ` u ) e. RR')], '( log ` u ) e. CC'), lift(w, d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0'), Ah)], '( ( log ` u ) ^ ( J + 1 ) ) e. CC'),
                             dd('cxpcld', [dd('rpcnd', [up], 'u e. CC'), dd('negcld', [lift(w, d('recnd', [er], 'E e. CC'), Ah)], '-u E e. CC')], '( u ^c -u E ) e. CC')], '%s e. CC' % PHu)
    def psc_(Ah, up):
        dd = lambda ref, h, c: D(w, Ah, ref, h, c)
        lg = dd('relogcld', [up], '( log ` u ) e. RR')
        return dd('recnd', [dd('remulcld', [dd('remulcld', [dd('rpred', [dd('rpcxpcld', [up, dd('resubcld', [dd('renegcld', [a1(w, Ah, '1re', '1 e. RR')], '-u 1 e. RR'), lift(w, er, Ah)], '( -u 1 - E ) e. RR')], '( u ^c ( -u 1 - E ) ) e. RR+')],
                                                                 '( u ^c ( -u 1 - E ) ) e. RR'), dd('reexpcld', [lg, lift(w, jn, Ah)], '( ( log ` u ) ^ J ) e. RR')], '( ( u ^c ( -u 1 - E ) ) x. ( ( log ` u ) ^ J ) ) e. RR'),
                                            dd('resubcld', [dd('peano2red' if False else 'readdcld', [dd('nn0red', [lift(w, jn, Ah)], 'J e. RR'), a1(w, Ah, '1re', '1 e. RR')], '( J + 1 ) e. RR'),
                                                            dd('remulcld', [lift(w, er, Ah), lg], '( E x. ( log ` u ) ) e. RR')], '( ( J + 1 ) - ( E x. ( log ` u ) ) ) e. RR')], '%s e. RR' % PSu)], '%s e. CC' % PSu)
    phcont = contdv(w, A0, PHu, dvf, psc_(Ar, upr), phc_(Ar, upr))
    # per prime p
    Ap = '( %s /\\ p e. %s )' % (A0, PZ)
    dp = lambda ref, h, c: D(w, Ap, ref, h, c)
    L = lambda st: lift(w, st, Ap)
    pm = psmem(w, Ap, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PZ)), 'Y', 'Z')
    pn = pm['pn']; prr = dp('nnred', [pn], 'p e. RR'); prp = dp('nnrpd', [pn], 'p e. RR+')
    pz_ = dp('letrd', [prr, dp('zred', [dp('flcld', [L(zr)], '( |_ ` Z ) e. ZZ')], '( |_ ` Z ) e. RR'), L(zr), pm['pl'], dp('syl', [L(zr), w.inst('flle')], '( |_ ` Z ) <_ Z')], 'p <_ Z')
    icr, ior = rpsets(w, Ap, prp, L(zr))
    gcont = restr(w, Ap, L(phcont), ('( p [,] Z )', icr), PHu)
    hcont = restr(w, Ap, L(psc), ('( p [,] Z )', icr), PSu)
    Apu = '( %s /\\ u e. RR+ )' % Ap
    upp = w.s([], 'simpr', '( %s -> u e. RR+ )' % Apu)
    dres = dp('dvmptres', [a1(w, Ap, 'reelprrecn', 'RR e. { RR , CC }'), phc_(Apu, upp), psc_(Apu, upp), L(dvf), ior, w.s([], 'eqid', '( ( TopOpen ` CCfld ) |`t RR ) = ( ( TopOpen ` CCfld ) |`t RR )'),
                          w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )'), open_ioo(w, Ap, 'p', 'Z')],
              '( RR _D ( u e. ( p (,) Z ) |-> %s ) ) = ( u e. ( p (,) Z ) |-> %s )' % (PHu, PSu))
    e5 = w.s([w.s([w.s([], 'fveq2', '( u = p -> ( log ` u ) = ( log ` p ) )')], 'oveq1d', '( u = p -> ( ( log ` u ) ^ ( J + 1 ) ) = ( ( log ` p ) ^ ( J + 1 ) ) )'),
              w.s([], 'oveq1', '( u = p -> ( u ^c -u E ) = ( p ^c -u E ) )')], 'oveq12d', '( u = p -> %s = %s )' % (PHu, PHI('J', 'p')))
    e6 = w.s([w.s([w.s([], 'fveq2', '( u = Z -> ( log ` u ) = ( log ` Z ) )')], 'oveq1d', '( u = Z -> ( ( log ` u ) ^ ( J + 1 ) ) = ( ( log ` Z ) ^ ( J + 1 ) ) )'),
              w.s([], 'oveq1', '( u = Z -> ( u ^c -u E ) = ( Z ^c -u E ) )')], 'oveq12d', '( u = Z -> %s = %s )' % (PHu, PHI('J', 'Z')))
    ftc = dp('ef1ftc', [dp('3jca', [prr, L(zr), pz_], '( p e. RR /\\ Z e. RR /\\ p <_ Z )'), gcont, dres, hcont, e5, e6],
             '( ( u e. ( p (,) Z ) |-> %s ) e. L^1 /\\ S. ( p (,) Z ) %s _d u = ( %s - %s ) )' % (PSu, PSu, PHI('J', 'Z'), PHI('J', 'p')))
    Apy = '( %s /\\ u e. %s )' % (Ap, YZ)
    uyz = w.s([], 'simpr', '( %s -> u e. %s )' % (Apy, YZ))
    uyp = D(w, Apy, 'elrpd', [D(w, Apy, 'syl', [uyz, w.inst('elioore')], 'u e. RR'),
                              D(w, Apy, 'ltletrd' if False else 'lttrd' if False else 'ltletrd', [a1(w, Apy, '0re', '0 e. RR'), lift(w, yr, Apy), D(w, Apy, 'syl', [uyz, w.inst('elioore')], 'u e. RR'),
                                                                                                  D(w, Apy, 'rpgt0d', [lift(w, yp, Apy)], '0 < Y'), D(w, Apy, 'ltled', [lift(w, yr, Apy), D(w, Apy, 'syl', [uyz, w.inst('elioore')], 'u e. RR'),
                                                                                                                                                                         D(w, Apy, 'simpld', [D(w, Apy, 'syl', [uyz, w.inst('eliooord')], '( Y < u /\\ u < Z )')], 'Y < u')], 'Y <_ u')],
                                '0 < u')], 'u e. RR+')
    ind = D(w, Ap, 'kd2ind', [dp('jca', [L(yr), L(zr)], '( Y e. RR /\\ Z e. RR )'), dp('3jca', [prr, pm['yp'], pz_], '( p e. RR /\\ Y < p /\\ p <_ Z )'), dp('simpld', [ftc], '( u e. ( p (,) Z ) |-> %s ) e. L^1' % PSu),
                              psc_(Apy, uyp)],
            '( ( u e. %s |-> if ( p <_ u , %s , 0 ) ) e. L^1 /\\ S. %s if ( p <_ u , %s , 0 ) _d u = S. ( p (,) Z ) %s _d u )' % (YZ, PSu, YZ, PSu, PSu))
    IF = 'if ( p <_ u , %s , 0 )' % PSu
    cpp = cpcc(w, Ap, 'p', pn, L(nxh), L(tr))
    ifc = D(w, Apy, 'ifcld', [psc_(Apy, uyp), a1(w, Apy, '0cn', '0 e. CC')], '%s e. CC' % IF)
    ibp = dp('iblmulc2', [cpp, ifc, dp('simpld', [ind], '( u e. %s |-> %s ) e. L^1' % (YZ, IF))], '( u e. %s |-> ( %s x. %s ) ) e. L^1' % (YZ, CP('p'), IF))
    itp = dp('eqtrd', [dp('itgmulc2', [cpp, ifc, dp('simpld', [ind], '( u e. %s |-> %s ) e. L^1' % (YZ, IF))], '( %s x. S. %s %s _d u ) = S. %s ( %s x. %s ) _d u' % (CP('p'), YZ, IF, YZ, CP('p'), IF))] if False else
                      [dp('eqcomd', [dp('itgmulc2', [cpp, ifc, dp('simpld', [ind], '( u e. %s |-> %s ) e. L^1' % (YZ, IF))], '( %s x. S. %s %s _d u ) = S. %s ( %s x. %s ) _d u' % (CP('p'), YZ, IF, YZ, CP('p'), IF))],
                          'S. %s ( %s x. %s ) _d u = ( %s x. S. %s %s _d u )' % (YZ, CP('p'), IF, CP('p'), YZ, IF)),
                       dp('oveq2d', [dp('eqtrd', [dp('simprd', [ind], 'S. %s %s _d u = S. ( p (,) Z ) %s _d u' % (YZ, IF, PSu)), dp('simprd', [ftc], 'S. ( p (,) Z ) %s _d u = ( %s - %s )' % (PSu, PHI('J', 'Z'), PHI('J', 'p')))],
                                                 'S. %s %s _d u = ( %s - %s )' % (YZ, IF, PHI('J', 'Z'), PHI('J', 'p')))], '( %s x. S. %s %s _d u ) = ( %s x. ( %s - %s ) )' % (CP('p'), YZ, IF, CP('p'), PHI('J', 'Z'), PHI('J', 'p')))],
            'S. %s ( %s x. %s ) _d u = ( %s x. ( %s - %s ) )' % (YZ, CP('p'), IF, CP('p'), PHI('J', 'Z'), PHI('J', 'p')))
    # itgfsum
    C_ = '( %s x. %s )' % (CP('p'), IF)
    Aup = '( %s /\\ ( u e. %s /\\ p e. %s ) )' % (A0, YZ, PZ)
    du = lambda ref, h, c: D(w, Aup, ref, h, c)
    pz2 = w.s([], 'simprr', '( %s -> p e. %s )' % (Aup, PZ)); uz2 = w.s([], 'simprl', '( %s -> u e. %s )' % (Aup, YZ))
    pm2 = psmem(w, Aup, 'p', pz2, 'Y', 'Z')
    ur2 = du('syl', [uz2, w.inst('elioore')], 'u e. RR')
    up2 = du('elrpd', [ur2, du('ltletrd', [a1(w, Aup, '0re', '0 e. RR'), lift(w, yr, Aup), ur2, du('rpgt0d', [lift(w, yp, Aup)], '0 < Y'),
                                          du('ltled', [lift(w, yr, Aup), ur2, du('simpld', [du('syl', [uz2, w.inst('eliooord')], '( Y < u /\\ u < Z )')], 'Y < u')], 'Y <_ u')], '0 < u')], 'u e. RR+')
    cc2 = du('mulcld', [cpcc(w, Aup, 'p', pm2['pn'], lift(w, nxh, Aup), lift(w, tr, Aup)), du('ifcld', [psc_(Aup, up2), a1(w, Aup, '0cn', '0 e. CC')], '%s e. CC' % IF)], '%s e. CC' % C_)
    pzf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` Z ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PZ)], '%s e. Fin' % PZ)
    ifs = d('itgfsum', [a1(w, A0, 'ioombl', '%s e. dom vol' % YZ), pzf, cc2, ibp],
            '( ( u e. %s |-> sum_ p e. %s %s ) e. L^1 /\\ S. %s sum_ p e. %s %s _d u = sum_ p e. %s S. %s %s _d u )' % (YZ, PZ, C_, YZ, PZ, C_, PZ, YZ, C_))
    s1 = d('sumeq2dv', [itp], 'sum_ p e. %s S. %s %s _d u = sum_ p e. %s ( %s x. ( %s - %s ) )' % (PZ, YZ, C_, PZ, CP('p'), PHI('J', 'Z'), PHI('J', 'p')))
    PZZ = PHI('J', 'Z')
    zp_ = d('elrpd', [zr, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), yr, zr, d('rpgt0d', [yp], '0 < Y'), yz], '0 < Z')], 'Z e. RR+')
    phz = d('mulcld', [d('expcld', [d('recnd', [d('relogcld', [zp_], '( log ` Z ) e. RR')], '( log ` Z ) e. CC'), d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')], '( ( log ` Z ) ^ ( J + 1 ) ) e. CC'),
                       d('cxpcld', [d('rpcnd', [zp_], 'Z e. CC'), d('negcld', [d('recnd', [er], 'E e. CC')], '-u E e. CC')], '( Z ^c -u E ) e. CC')], '%s e. CC' % PZZ)
    php = phc_(Ap, prp) if False else None
    Ap2 = Ap
    phpc = dp('mulcld', [dp('expcld', [dp('recnd', [dp('relogcld', [prp], '( log ` p ) e. RR')], '( log ` p ) e. CC'), L(d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0'))], '( ( log ` p ) ^ ( J + 1 ) ) e. CC'),
                         dp('cxpcld', [dp('rpcnd', [prp], 'p e. CC'), dp('negcld', [L(d('recnd', [er], 'E e. CC'))], '-u E e. CC')], '( p ^c -u E ) e. CC')], '%s e. CC' % PHI('J', 'p'))
    clt = Closure(w, Ap, {CP('p'): ('CC', cpp), PZZ: ('CC', L(phz)), PHI('J', 'p'): ('CC', phpc)})
    for a in (CP('p'), PZZ, PHI('J', 'p')):
        clt.atom(a)
    tq = ringeq(w, Ap, '( %s x. ( %s - %s ) )' % (CP('p'), PZZ, PHI('J', 'p')), '( ( %s x. %s ) - ( %s x. %s ) )' % (PZZ, CP('p'), PHI('J', 'p'), CP('p')), clt)
    s2 = d('sumeq2dv', [tq], 'sum_ p e. %s ( %s x. ( %s - %s ) ) = sum_ p e. %s ( ( %s x. %s ) - ( %s x. %s ) )' % (PZ, CP('p'), PZZ, PHI('J', 'p'), PZ, PZZ, CP('p'), PHI('J', 'p'), CP('p')))
    s3 = d('fsumsub', [pzf, dp('mulcld', [L(phz), cpp], '( %s x. %s ) e. CC' % (PZZ, CP('p'))), dp('mulcld', [phpc, cpp], '( %s x. %s ) e. CC' % (PHI('J', 'p'), CP('p')))],
           'sum_ p e. %s ( ( %s x. %s ) - ( %s x. %s ) ) = ( sum_ p e. %s ( %s x. %s ) - %s )' % (PZ, PZZ, CP('p'), PHI('J', 'p'), CP('p'), PZ, PZZ, CP('p'), DWIN('J', 'Y', 'Z')))
    s4 = d('fsummulc2', [pzf, phz, cpp], '( %s x. %s ) = sum_ p e. %s ( %s x. %s )' % (PZZ, PWS('T', 'Y', 'Z'), PZ, PZZ, CP('p')))
    SUMC = 'sum_ p e. %s %s' % (PZ, C_)
    RHS = '( ( %s x. %s ) - %s )' % (PZZ, PWS('T', 'Y', 'Z'), DWIN('J', 'Y', 'Z'))
    ival = chain(w, A0, ['S. %s %s _d u' % (YZ, SUMC), 'sum_ p e. %s S. %s %s _d u' % (PZ, YZ, C_), 'sum_ p e. %s ( %s x. ( %s - %s ) )' % (PZ, CP('p'), PZZ, PHI('J', 'p')),
                         'sum_ p e. %s ( ( %s x. %s ) - ( %s x. %s ) )' % (PZ, PZZ, CP('p'), PHI('J', 'p'), CP('p')), '( sum_ p e. %s ( %s x. %s ) - %s )' % (PZ, PZZ, CP('p'), DWIN('J', 'Y', 'Z')), RHS],
                 [d('simprd', [ifs], 'S. %s %s _d u = sum_ p e. %s S. %s %s _d u' % (YZ, SUMC, PZ, YZ, C_)), s1, s2, s3,
                  d('oveq1d', [d('eqcomd', [s4], 'sum_ p e. %s ( %s x. %s ) = ( %s x. %s )' % (PZ, PZZ, CP('p'), PZZ, PWS('T', 'Y', 'Z')))],
                    '( sum_ p e. %s ( %s x. %s ) - %s ) = %s' % (PZ, PZZ, CP('p'), DWIN('J', 'Y', 'Z'), RHS))])
    # pointwise psi . S ( u ) = sum_ p C
    Ay = '( %s /\\ u e. %s )' % (A0, YZ)
    dy = lambda ref, h, c: D(w, Ay, ref, h, c)
    uy = w.s([], 'simpr', '( %s -> u e. %s )' % (Ay, YZ))
    ury = dy('syl', [uy, w.inst('elioore')], 'u e. RR')
    uzy = dy('ltled', [ury, lift(w, zr, Ay), dy('simprd', [dy('syl', [uy, w.inst('eliooord')], '( Y < u /\\ u < Z )')], 'u < Z')], 'u <_ Z')
    upy = dy('elrpd', [ury, dy('ltletrd', [a1(w, Ay, '0re', '0 e. RR'), lift(w, yr, Ay), ury, dy('rpgt0d', [lift(w, yp, Ay)], '0 < Y'),
                                          dy('ltled', [lift(w, yr, Ay), ury, dy('simpld', [dy('syl', [uy, w.inst('eliooord')], '( Y < u /\\ u < Z )')], 'Y < u')], 'Y <_ u')], '0 < u')], 'u e. RR+')
    PWu = PWS('T', 'Y', 'u')
    pif = use(w, Ay, 'kd2pwsif', {'U': 'u'}, dy('3jca', [lift(w, nxh, Ay), dy('jca', [lift(w, tr, Ay), lift(w, yr, Ay)], '( T e. RR /\\ Y e. RR )'), dy('3jca', [lift(w, zr, Ay), ury, uzy], '( Z e. RR /\\ u e. RR /\\ u <_ Z )')],
                                                    '( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( Z e. RR /\\ u e. RR /\\ u <_ Z ) )' % NXH))
    IFC = 'if ( p <_ u , %s , 0 )' % CP('p')
    Ayp = '( %s /\\ p e. %s )' % (Ay, PZ)
    pm3 = psmem(w, Ayp, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ayp, PZ)), 'Y', 'Z')
    cp3 = cpcc(w, Ayp, 'p', pm3['pn'], lift(w, nxh, Ayp), lift(w, tr, Ayp))
    ps3 = psc_(Ayp, lift(w, upy, Ayp))
    ifcc3 = D(w, Ayp, 'ifcld', [cp3, a1(w, Ayp, '0cn', '0 e. CC')], '%s e. CC' % IFC)
    fm = dy('fsummulc2', [lift(w, pzf, Ay), psc_(Ay, upy), ifcc3], '( %s x. sum_ p e. %s %s ) = sum_ p e. %s ( %s x. %s )' % (PSu, PZ, IFC, PZ, PSu, IFC))
    Ac = '( %s /\\ p <_ u )' % Ayp
    t_ = D(w, Ac, 'eqtr4d', [D(w, Ac, 'eqtrd', [D(w, Ac, 'oveq2d', [D(w, Ac, 'syl', [w.s([], 'simpr', '( %s -> p <_ u )' % Ac), w.inst('iftrue')], '%s = %s' % (IFC, CP('p')))], '( %s x. %s ) = ( %s x. %s )' % (PSu, IFC, PSu, CP('p'))),
                                                D(w, Ac, 'mulcomd', [lift(w, ps3, Ac), lift(w, cp3, Ac)], '( %s x. %s ) = ( %s x. %s )' % (PSu, CP('p'), CP('p'), PSu))], '( %s x. %s ) = ( %s x. %s )' % (PSu, IFC, CP('p'), PSu)),
                             D(w, Ac, 'oveq2d', [D(w, Ac, 'syl', [w.s([], 'simpr', '( %s -> p <_ u )' % Ac), w.inst('iftrue')], '%s = %s' % (IF, PSu))], '%s = ( %s x. %s )' % (C_, CP('p'), PSu))],
           '( %s x. %s ) = %s' % (PSu, IFC, C_))
    An_ = '( %s /\\ -. p <_ u )' % Ayp
    f_ = D(w, An_, 'eqtr4d', [D(w, An_, 'eqtrd', [D(w, An_, 'oveq2d', [D(w, An_, 'syl', [w.s([], 'simpr', '( %s -> -. p <_ u )' % An_), w.inst('iffalse')], '%s = 0' % IFC)], '( %s x. %s ) = ( %s x. 0 )' % (PSu, IFC, PSu)),
                                                  D(w, An_, 'mul01d', [lift(w, ps3, An_)], '( %s x. 0 ) = 0' % PSu)], '( %s x. %s ) = 0' % (PSu, IFC)),
                              D(w, An_, 'eqtrd', [D(w, An_, 'oveq2d', [D(w, An_, 'syl', [w.s([], 'simpr', '( %s -> -. p <_ u )' % An_), w.inst('iffalse')], '%s = 0' % IF)], '%s = ( %s x. 0 )' % (C_, CP('p'))),
                                                  D(w, An_, 'mul01d', [lift(w, cp3, An_)], '( %s x. 0 ) = 0' % CP('p'))], '%s = 0' % C_)],
           '( %s x. %s ) = %s' % (PSu, IFC, C_))
    tf = D(w, Ayp, 'pm2.61dan', [t_, f_], '( %s x. %s ) = %s' % (PSu, IFC, C_))
    pw1 = chain(w, Ay, ['( %s x. %s )' % (PSu, PWu), '( %s x. sum_ p e. %s %s )' % (PSu, PZ, IFC), 'sum_ p e. %s ( %s x. %s )' % (PZ, PSu, IFC), SUMC],
                [dy('oveq2d', [pif], '( %s x. %s ) = ( %s x. sum_ p e. %s %s )' % (PSu, PWu, PSu, PZ, IFC)), fm, dy('sumeq2dv', [tf], 'sum_ p e. %s ( %s x. %s ) = %s' % (PZ, PSu, IFC, SUMC))])
    meq = d('mpteq2dva', [pw1], '( u e. %s |-> ( %s x. %s ) ) = ( u e. %s |-> %s )' % (YZ, PSu, PWu, YZ, SUMC))
    ibl = d('eqeltrd', [meq, d('simpld', [ifs], '( u e. %s |-> %s ) e. L^1' % (YZ, SUMC))], '( u e. %s |-> ( %s x. %s ) ) e. L^1' % (YZ, PSu, PWu))
    ieq = d('eqtrd', [d('itgeq2dv', [pw1], 'S. %s ( %s x. %s ) _d u = S. %s %s _d u' % (YZ, PSu, PWu, YZ, SUMC)), ival], 'S. %s ( %s x. %s ) _d u = %s' % (YZ, PSu, PWu, RHS))
    pwzc = d('fsumcl', [pzf, cpp], '%s e. CC' % PWS('T', 'Y', 'Z'))
    dwc = d('fsumcl', [pzf, dp('mulcld', [phpc, cpp], '( %s x. %s ) e. CC' % (PHI('J', 'p'), CP('p')))], '%s e. CC' % DWIN('J', 'Y', 'Z'))
    A_ = '( %s x. %s )' % (PZZ, PWS('T', 'Y', 'Z'))
    nc = d('nncand', [d('mulcld', [phz, pwzc], '%s e. CC' % A_), dwc], '( %s - %s ) = %s' % (A_, RHS, DWIN('J', 'Y', 'Z')))
    dwe = d('eqtrd', [nc, d('oveq2d', [ieq], '( %s - S. %s ( %s x. %s ) _d u ) = ( %s - %s )' % (A_, YZ, PSu, PWu, A_, RHS))] if False else
            [d('oveq2d', [ieq], '( %s - S. %s ( %s x. %s ) _d u ) = ( %s - %s )' % (A_, YZ, PSu, PWu, A_, RHS)), nc], '( %s - S. %s ( %s x. %s ) _d u ) = %s' % (A_, YZ, PSu, PWu, DWIN('J', 'Y', 'Z')))
    fin = d('jca', [ibl, d('eqcomd', [dwe], '%s = ( %s - S. %s ( %s x. %s ) _d u )' % (DWIN('J', 'Y', 'Z'), A_, YZ, PSu, PWu))], S['kd2abel'].split(' -> ', 1)[1][:-2])
    w.qed([fin], 'idi', S['kd2abel'])
    return only_run(w, only)


def pwscong(w, x, y):
    """closed ( x = y -> PWS(T,Y,x) = PWS(T,Y,y) )"""
    H = '%s = %s' % (x, y)
    a = w.s([], 'fveq2', '( %s -> ( |_ ` %s ) = ( |_ ` %s ) )' % (H, x, y))
    b = w.s([a], 'oveq2d', '( %s -> ( 1 ... ( |_ ` %s ) ) = ( 1 ... ( |_ ` %s ) ) )' % (H, x, y))
    c = w.s([b], 'rabeqdv', '( %s -> %s = %s )' % (H, PSET('Y', x), PSET('Y', y)))
    return w.s([c], 'sumeq1d', '( %s -> %s = %s )' % (H, PWS('T', 'Y', x), PWS('T', 'Y', y)))


def gen_ibl():
    w = W('kd2ibl', 'The mean-square integrand ` abs S ( u )^2 / u ` of the window sum is integrable on ` ( X1 , X2 ) ` ( ~ bddmulibl : ` S ` is a bounded finite sum of indicator steps, ` conj S / u ` is integrable by ~ kd2ind ; Lean ` hIint ` ).')
    from kd2_e import psmem, cpcc
    A0 = S['kd2ibl'].split(' -> ( u e.')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    nxh = d('simp1', [], NXH); tr = d('simp2', [], 'T e. RR'); g3 = d('simp3', [], '( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z )')
    yp = d('simp1d', [g3], 'Y e. RR+'); zr = d('simp2d', [g3], 'Z e. RR'); yz = d('simp3d', [g3], 'Y <_ Z')
    yr = d('rpred', [yp], 'Y e. RR')
    YZ = '( Y (,) Z )'; PZ = PSET('Y', 'Z')
    pzf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` Z ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PZ)], '%s e. Fin' % PZ)
    Ap = '( %s /\\ p e. %s )' % (A0, PZ)
    dp = lambda ref, h, c: D(w, Ap, ref, h, c)
    L = lambda st: lift(w, st, Ap)
    pm = psmem(w, Ap, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PZ)), 'Y', 'Z')
    pn = pm['pn']; prr = dp('nnred', [pn], 'p e. RR'); prp = dp('nnrpd', [pn], 'p e. RR+')
    pz_ = dp('letrd', [prr, dp('zred', [dp('flcld', [L(zr)], '( |_ ` Z ) e. ZZ')], '( |_ ` Z ) e. RR'), L(zr), pm['pl'], dp('syl', [L(zr), w.inst('flle')], '( |_ ` Z ) <_ Z')], 'p <_ Z')
    cpp = cpcc(w, Ap, 'p', pn, L(nxh), L(tr))
    CJ = '( * ` %s )' % CP('p')
    cjc = dp('cjcld', [cpp], '%s e. CC' % CJ)
    PZI = '( p (,) Z )'
    # constant on ( p , Z )
    ic1 = dp('syl3anc', [a1(w, Ap, 'ioombl', '%s e. dom vol' % PZI), dp('syl2anc', [prr, L(zr), w.inst('ioovolcl')], '( vol ` %s ) e. RR' % PZI), cpp, w.inst('iblconst')], '( %s X. { %s } ) e. L^1' % (PZI, CP('p')))
    ic2 = dp('eqeltrrd' if False else 'eqeltrd', [a1(w, Ap, 'fconstmpt', '( %s X. { %s } ) = ( t e. %s |-> %s )' % (PZI, CP('p'), PZI, CP('p'))) if False else
                                                   w.s([w.s([w.s([], 'fconstmpt', '( %s X. { %s } ) = ( t e. %s |-> %s )' % (PZI, CP('p'), PZI, CP('p')))], 'eqcomi', '( t e. %s |-> %s ) = ( %s X. { %s } )' % (PZI, CP('p'), PZI, CP('p')))],
                                                       'a1i', '( %s -> ( t e. %s |-> %s ) = ( %s X. { %s } ) )' % (Ap, PZI, CP('p'), PZI, CP('p'))), ic1], '( t e. %s |-> %s ) e. L^1' % (PZI, CP('p')))
    Apt = '( %s /\\ t e. %s )' % (Ap, YZ)
    ind1 = D(w, Ap, 'kd2ind', [dp('jca', [L(yr), L(zr)], '( Y e. RR /\\ Z e. RR )'), dp('3jca', [prr, pm['yp'], pz_], '( p e. RR /\\ Y < p /\\ p <_ Z )'), ic2, lift(w, cpp, Apt)],
             '( ( t e. %s |-> if ( p <_ t , %s , 0 ) ) e. L^1 /\\ S. %s if ( p <_ t , %s , 0 ) _d t = S. %s %s _d t )' % (YZ, CP('p'), YZ, CP('p'), PZI, CP('p')))
    # conj / t on ( p , Z )
    from kd2_g import rpsets
    icr, ior = rpsets(w, Ap, prp, L(zr))
    ncz = "( CC \\ { 0 } )"
    Ai = '( %s /\\ t e. ( p [,] Z ) )' % Ap
    tin = D(w, Ai, 'sseldd', [lift(w, icr, Ai), w.s([], 'simpr', '( %s -> t e. ( p [,] Z ) )' % Ai)], 't e. RR+')
    iss = dp('ssrdv', [w.s([D(w, Ai, 'syl', [tin, w.inst('rpcndif0')], 't e. %s' % ncz)], 'ex', '( %s -> ( t e. ( p [,] Z ) -> t e. %s ) )' % (Ap, ncz))], '( p [,] Z ) C_ %s' % ncz)
    idc = dp('syl', [dp('jca', [iss, a1(w, Ap, 'difss', '%s C_ CC' % ncz)], '( ( p [,] Z ) C_ %s /\\ %s C_ CC )' % (ncz, ncz)), w.inst('cncfmptid')], '( t e. ( p [,] Z ) |-> t ) e. ( ( p [,] Z ) -cn-> %s )' % ncz)
    icb = dp('sstrd', [icr, dp('sstrd', [a1(w, Ap, 'rpssre', 'RR+ C_ RR'), a1(w, Ap, 'ax-resscn', 'RR C_ CC')], 'RR+ C_ CC')], '( p [,] Z ) C_ CC')
    cst = dp('syl', [dp('3jca', [cjc, icb, dp('ssidd', [], 'CC C_ CC')], '( %s e. CC /\\ ( p [,] Z ) C_ CC /\\ CC C_ CC )' % CJ), w.inst('cncfmptc')], '( t e. ( p [,] Z ) |-> %s ) e. ( ( p [,] Z ) -cn-> CC )' % CJ)
    Q = '( %s / t )' % CJ
    qc = dp('divcncf', [cst, idc], '( t e. ( p [,] Z ) |-> %s ) e. ( ( p [,] Z ) -cn-> CC )' % Q)
    qib = dp('syl3anc', [prr, L(zr), qc, w.inst('cniccibl')], '( t e. ( p [,] Z ) |-> %s ) e. L^1' % Q)
    qc2 = D(w, Ai, 'divcld', [lift(w, cjc, Ai), D(w, Ai, 'rpcnd', [tin], 't e. CC'), D(w, Ai, 'rpne0d', [tin], 't =/= 0')], '%s e. CC' % Q)
    qib2 = dp('iblss', [a1(w, Ap, 'ioossicc', '%s C_ ( p [,] Z )' % PZI), a1(w, Ap, 'ioombl', '%s e. dom vol' % PZI), qc2, qib], '( t e. %s |-> %s ) e. L^1' % (PZI, Q))
    Aty = '( %s /\\ t e. %s )' % (Ap, YZ)
    ty = w.s([], 'simpr', '( %s -> t e. %s )' % (Aty, YZ))
    tyr = D(w, Aty, 'syl', [ty, w.inst('elioore')], 't e. RR')
    typ = D(w, Aty, 'elrpd', [tyr, D(w, Aty, 'ltletrd', [a1(w, Aty, '0re', '0 e. RR'), lift(w, yr, Aty), tyr, D(w, Aty, 'rpgt0d', [lift(w, yp, Aty)], '0 < Y'),
                                                      D(w, Aty, 'ltled', [lift(w, yr, Aty), tyr, D(w, Aty, 'simpld', [D(w, Aty, 'syl', [ty, w.inst('eliooord')], '( Y < t /\\ t < Z )')], 'Y < t')], 'Y <_ t')], '0 < t')], 't e. RR+')
    qc3 = D(w, Aty, 'divcld', [lift(w, cjc, Aty), D(w, Aty, 'rpcnd', [typ], 't e. CC'), D(w, Aty, 'rpne0d', [typ], 't =/= 0')], '%s e. CC' % Q)
    ind2 = D(w, Ap, 'kd2ind', [dp('jca', [L(yr), L(zr)], '( Y e. RR /\\ Z e. RR )'), dp('3jca', [prr, pm['yp'], pz_], '( p e. RR /\\ Y < p /\\ p <_ Z )'), qib2, qc3],
             '( ( t e. %s |-> if ( p <_ t , %s , 0 ) ) e. L^1 /\\ S. %s if ( p <_ t , %s , 0 ) _d t = S. %s %s _d t )' % (YZ, Q, YZ, Q, PZI, Q))
    I1 = 'if ( p <_ t , %s , 0 )' % CP('p'); I2 = 'if ( p <_ t , %s , 0 )' % Q
    Atp = '( %s /\\ ( t e. %s /\\ p e. %s ) )' % (A0, YZ, PZ)
    pz3 = w.s([], 'simprr', '( %s -> p e. %s )' % (Atp, PZ)); tz3 = w.s([], 'simprl', '( %s -> t e. %s )' % (Atp, YZ))
    pm3 = psmem(w, Atp, 'p', pz3, 'Y', 'Z')
    cp3 = cpcc(w, Atp, 'p', pm3['pn'], lift(w, nxh, Atp), lift(w, tr, Atp))
    t3r = D(w, Atp, 'syl', [tz3, w.inst('elioore')], 't e. RR')
    t3p = D(w, Atp, 'elrpd', [t3r, D(w, Atp, 'ltletrd', [a1(w, Atp, '0re', '0 e. RR'), lift(w, yr, Atp), t3r, D(w, Atp, 'rpgt0d', [lift(w, yp, Atp)], '0 < Y'),
                                                      D(w, Atp, 'ltled', [lift(w, yr, Atp), t3r, D(w, Atp, 'simpld', [D(w, Atp, 'syl', [tz3, w.inst('eliooord')], '( Y < t /\\ t < Z )')], 'Y < t')], 'Y <_ t')], '0 < t')], 't e. RR+')
    i1c = D(w, Atp, 'ifcld', [cp3, a1(w, Atp, '0cn', '0 e. CC')], '%s e. CC' % I1)
    i2c = D(w, Atp, 'ifcld', [D(w, Atp, 'divcld', [D(w, Atp, 'cjcld', [cp3], '%s e. CC' % CJ), D(w, Atp, 'rpcnd', [t3p], 't e. CC'), D(w, Atp, 'rpne0d', [t3p], 't =/= 0')], '%s e. CC' % Q),
                              a1(w, Atp, '0cn', '0 e. CC')], '%s e. CC' % I2)
    S1 = 'sum_ p e. %s %s' % (PZ, I1); S2 = 'sum_ p e. %s %s' % (PZ, I2)
    f1 = d('simpld', [d('itgfsum', [a1(w, A0, 'ioombl', '%s e. dom vol' % YZ), pzf, i1c, dp('simpld', [ind1], '( t e. %s |-> %s ) e. L^1' % (YZ, I1))],
                        '( ( t e. %s |-> %s ) e. L^1 /\\ S. %s %s _d t = sum_ p e. %s S. %s %s _d t )' % (YZ, S1, YZ, S1, PZ, YZ, I1))], '( t e. %s |-> %s ) e. L^1' % (YZ, S1))
    f2 = d('simpld', [d('itgfsum', [a1(w, A0, 'ioombl', '%s e. dom vol' % YZ), pzf, i2c, dp('simpld', [ind2], '( t e. %s |-> %s ) e. L^1' % (YZ, I2))],
                        '( ( t e. %s |-> %s ) e. L^1 /\\ S. %s %s _d t = sum_ p e. %s S. %s %s _d t )' % (YZ, S2, YZ, S2, PZ, YZ, I2))], '( t e. %s |-> %s ) e. L^1' % (YZ, S2))
    # pointwise
    Ay = '( %s /\\ t e. %s )' % (A0, YZ)
    dy = lambda ref, h, c: D(w, Ay, ref, h, c)
    ty2 = w.s([], 'simpr', '( %s -> t e. %s )' % (Ay, YZ))
    tr2 = dy('syl', [ty2, w.inst('elioore')], 't e. RR')
    tz2 = dy('ltled', [tr2, lift(w, zr, Ay), dy('simprd', [dy('syl', [ty2, w.inst('eliooord')], '( Y < t /\\ t < Z )')], 't < Z')], 't <_ Z')
    tp2 = dy('elrpd', [tr2, dy('ltletrd', [a1(w, Ay, '0re', '0 e. RR'), lift(w, yr, Ay), tr2, dy('rpgt0d', [lift(w, yp, Ay)], '0 < Y'),
                                          dy('ltled', [lift(w, yr, Ay), tr2, dy('simpld', [dy('syl', [ty2, w.inst('eliooord')], '( Y < t /\\ t < Z )')], 'Y < t')], 'Y <_ t')], '0 < t')], 't e. RR+')
    PWt = PWS('T', 'Y', 't')
    pif = use(w, Ay, 'kd2pwsif', {'U': 't'}, dy('3jca', [lift(w, nxh, Ay), dy('jca', [lift(w, tr, Ay), lift(w, yr, Ay)], '( T e. RR /\\ Y e. RR )'), dy('3jca', [lift(w, zr, Ay), tr2, tz2], '( Z e. RR /\\ t e. RR /\\ t <_ Z )')],
                                                    '( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( Z e. RR /\\ t e. RR /\\ t <_ Z ) )' % NXH))
    Ayp = '( %s /\\ p e. %s )' % (Ay, PZ)
    pm4 = psmem(w, Ayp, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ayp, PZ)), 'Y', 'Z')
    cp4 = cpcc(w, Ayp, 'p', pm4['pn'], lift(w, nxh, Ayp), lift(w, tr, Ayp))
    i1c4 = D(w, Ayp, 'ifcld', [cp4, a1(w, Ayp, '0cn', '0 e. CC')], '%s e. CC' % I1)
    cjs = dy('fsumcj', [lift(w, pzf, Ay), i1c4], '( * ` %s ) = sum_ p e. %s ( * ` %s )' % (S1, PZ, I1))
    tc2 = dy('rpcnd', [tp2], 't e. CC'); tn2 = dy('rpne0d', [tp2], 't =/= 0')
    dvs = dy('fsumdivc', [lift(w, pzf, Ay), tc2, D(w, Ayp, 'cjcld', [i1c4], '( * ` %s ) e. CC' % I1), tn2], '( sum_ p e. %s ( * ` %s ) / t ) = sum_ p e. %s ( ( * ` %s ) / t )' % (PZ, I1, PZ, I1))
    Ac = '( %s /\\ p <_ t )' % Ayp
    tt_ = D(w, Ac, 'eqtr4d', [D(w, Ac, 'oveq1d', [D(w, Ac, 'fveq2d', [D(w, Ac, 'syl', [w.s([], 'simpr', '( %s -> p <_ t )' % Ac), w.inst('iftrue')], '%s = %s' % (I1, CP('p')))], '( * ` %s ) = %s' % (I1, CJ))],
                                                '( ( * ` %s ) / t ) = %s' % (I1, Q)),
                              D(w, Ac, 'syl', [w.s([], 'simpr', '( %s -> p <_ t )' % Ac), w.inst('iftrue')], '%s = %s' % (I2, Q))], '( ( * ` %s ) / t ) = %s' % (I1, I2))
    An_ = '( %s /\\ -. p <_ t )' % Ayp
    ff_ = D(w, An_, 'eqtr4d', [D(w, An_, 'eqtrd', [D(w, An_, 'oveq1d', [D(w, An_, 'eqtrd', [D(w, An_, 'fveq2d', [D(w, An_, 'syl', [w.s([], 'simpr', '( %s -> -. p <_ t )' % An_), w.inst('iffalse')], '%s = 0' % I1)], '( * ` %s ) = ( * ` 0 )' % I1),
                                                                                           a1(w, An_, 'cj0', '( * ` 0 ) = 0')], '( * ` %s ) = 0' % I1)], '( ( * ` %s ) / t ) = ( 0 / t )' % I1),
                                                  D(w, An_, 'div0d', [lift(w, tc2, An_), lift(w, tn2, An_)], '( 0 / t ) = 0')], '( ( * ` %s ) / t ) = 0' % I1),
                               D(w, An_, 'syl', [w.s([], 'simpr', '( %s -> -. p <_ t )' % An_), w.inst('iffalse')], '%s = 0' % I2)], '( ( * ` %s ) / t ) = %s' % (I1, I2))
    tf = D(w, Ayp, 'pm2.61dan', [tt_, ff_], '( ( * ` %s ) / t ) = %s' % (I1, I2))
    g2p = chain(w, Ay, ['( ( * ` %s ) / t )' % PWt, '( ( * ` %s ) / t )' % S1, '( sum_ p e. %s ( * ` %s ) / t )' % (PZ, I1), 'sum_ p e. %s ( ( * ` %s ) / t )' % (PZ, I1), S2],
                [dy('oveq1d', [dy('fveq2d', [pif], '( * ` %s ) = ( * ` %s )' % (PWt, S1))], '( ( * ` %s ) / t ) = ( ( * ` %s ) / t )' % (PWt, S1)),
                 dy('oveq1d', [cjs], '( ( * ` %s ) / t ) = ( sum_ p e. %s ( * ` %s ) / t )' % (S1, PZ, I1)), dvs, dy('sumeq2dv', [tf], 'sum_ p e. %s ( ( * ` %s ) / t ) = %s' % (PZ, I1, S2))])
    F2 = '( t e. %s |-> %s )' % (YZ, PWt); G2 = '( t e. %s |-> ( ( * ` %s ) / t ) )' % (YZ, PWt)
    f2i = d('eqeltrd', [d('mpteq2dva', [pif], '%s = ( t e. %s |-> %s )' % (F2, YZ, S1)), f1], '%s e. L^1' % F2)
    g2i = d('eqeltrd', [d('mpteq2dva', [g2p], '%s = ( t e. %s |-> %s )' % (G2, YZ, S2)), f2], '%s e. L^1' % G2)
    # bound, at the letter u
    B_ = 'sum_ p e. %s ( abs ` %s )' % (PZ, CP('p'))
    br = d('fsumrecl', [pzf, dp('abscld', [cpp], '( abs ` %s ) e. RR' % CP('p'))], '%s e. RR' % B_)
    Au = '( %s /\\ u e. %s )' % (A0, YZ)
    du = lambda ref, h, c: D(w, Au, ref, h, c)
    uy = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, YZ))
    ur = du('syl', [uy, w.inst('elioore')], 'u e. RR')
    uz_ = du('ltled', [ur, lift(w, zr, Au), du('simprd', [du('syl', [uy, w.inst('eliooord')], '( Y < u /\\ u < Z )')], 'u < Z')], 'u <_ Z')
    PWu = PWS('T', 'Y', 'u'); PSu_ = PSET('Y', 'u')
    Apu = '( %s /\\ p e. %s )' % (Au, PSu_)
    pm5 = psmem(w, Apu, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Apu, PSu_)), 'Y', 'u')
    cp5 = cpcc(w, Apu, 'p', pm5['pn'], lift(w, nxh, Apu), lift(w, tr, Apu))
    Auz = '( %s /\\ p e. %s )' % (Au, PZ)
    pm6 = psmem(w, Auz, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Auz, PZ)), 'Y', 'Z')
    cp6 = cpcc(w, Auz, 'p', pm6['pn'], lift(w, nxh, Auz), lift(w, tr, Auz))
    psz = du('syl', [du('syl', [du('syl3anc', [ur, lift(w, zr, Au), uz_, w.inst('flword2')], '( |_ ` Z ) e. ( ZZ>= ` ( |_ ` u ) )'), w.inst('fzss2')], '( 1 ... ( |_ ` u ) ) C_ ( 1 ... ( |_ ` Z ) )'),
                     w.inst('rabss2')], '%s C_ %s' % (PSu_, PZ))
    psuf = du('ssfid', [du('fzfid', [], '( 1 ... ( |_ ` u ) ) e. Fin'), a1(w, Au, 'ssrab2', '%s C_ ( 1 ... ( |_ ` u ) )' % PSu_)], '%s e. Fin' % PSu_)
    ba = du('fsumabs', [psuf, cp5], '( abs ` %s ) <_ sum_ p e. %s ( abs ` %s )' % (PWu, PSu_, CP('p')))
    bb = du('fsumless', [lift(w, pzf, Au), D(w, Auz, 'abscld', [cp6], '( abs ` %s ) e. RR' % CP('p')), D(w, Auz, 'absge0d', [cp6], '0 <_ ( abs ` %s )' % CP('p')), psz],
            'sum_ p e. %s ( abs ` %s ) <_ %s' % (PSu_, CP('p'), B_))
    pwcu = du('fsumcl', [psuf, cp5], '%s e. CC' % PWu)
    bnd = du('letrd', [du('abscld', [pwcu], '( abs ` %s ) e. RR' % PWu), du('fsumrecl', [psuf, D(w, Apu, 'abscld', [cp5], '( abs ` %s ) e. RR' % CP('p'))], 'sum_ p e. %s ( abs ` %s ) e. RR' % (PSu_, CP('p'))),
                       lift(w, br, Au), ba, bb], '( abs ` %s ) <_ %s' % (PWu, B_))
    fv = du('fvmptd', [a1(w, Au, 'eqid', '%s = %s' % (F2, F2)), w.s([pwscong(w, 't', 'u')], 'adantl', '( ( %s /\\ t = u ) -> %s = %s )' % (Au, PWt, PWu)), uy, pwcu], '( %s ` u ) = %s' % (F2, PWu))
    bnd2 = du('eqbrtrd', [du('fveq2d', [fv], '( abs ` ( %s ` u ) ) = ( abs ` %s )' % (F2, PWu)), bnd], '( abs ` ( %s ` u ) ) <_ %s' % (F2, B_))
    ral = d('ralrimiva', [bnd2], 'A. u e. %s ( abs ` ( %s ` u ) ) <_ %s' % (YZ, F2, B_))
    pwc = dy('fsumcl', [dy('ssfid', [dy('fzfid', [], '( 1 ... ( |_ ` t ) ) e. Fin'), a1(w, Ay, 'ssrab2', '%s C_ ( 1 ... ( |_ ` t ) )' % PSET('Y', 't'))], '%s e. Fin' % PSET('Y', 't')),
                        cpcc(w, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't')), 'p', psmem(w, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't')), 'p', w.s([], 'simpr', '( ( %s /\\ p e. %s ) -> p e. %s )' % (Ay, PSET('Y', 't'), PSET('Y', 't'))), 'Y', 't')['pn'],
                             lift(w, nxh, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't'))), lift(w, tr, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't'))))], '%s e. CC' % PWt)
    dmf = d('dmmptd', [w.s([], 'eqid', '%s = %s' % (F2, F2)), pwc], 'dom %s = %s' % (F2, YZ))
    ral2 = d('mpbird', [ral, d('raleqdv', [dmf], '( A. u e. dom %s ( abs ` ( %s ` u ) ) <_ %s <-> A. u e. %s ( abs ` ( %s ` u ) ) <_ %s )' % (F2, F2, B_, YZ, F2, B_))],
             'A. u e. dom %s ( abs ` ( %s ` u ) ) <_ %s' % (F2, F2, B_))
    rv = w.s([w.s([], 'breq2', '( v = %s -> ( ( abs ` ( %s ` u ) ) <_ v <-> ( abs ` ( %s ` u ) ) <_ %s ) )' % (B_, F2, F2, B_))], 'ralbidv',
             '( v = %s -> ( A. u e. dom %s ( abs ` ( %s ` u ) ) <_ v <-> A. u e. dom %s ( abs ` ( %s ` u ) ) <_ %s ) )' % (B_, F2, F2, F2, F2, B_))
    ex = d('syl', [d('jca', [br, ral2], '( %s e. RR /\\ A. u e. dom %s ( abs ` ( %s ` u ) ) <_ %s )' % (B_, F2, F2, B_)), w.s([rv], 'rspcev', '( ( %s e. RR /\\ A. u e. dom %s ( abs ` ( %s ` u ) ) <_ %s ) -> E. v e. RR A. u e. dom %s ( abs ` ( %s ` u ) ) <_ v )' % (B_, F2, F2, B_, F2, F2))],
           'E. v e. RR A. u e. dom %s ( abs ` ( %s ` u ) ) <_ v' % (F2, F2))
    pwc = dy('fsumcl', [dy('ssfid', [dy('fzfid', [], '( 1 ... ( |_ ` t ) ) e. Fin'), a1(w, Ay, 'ssrab2', '%s C_ ( 1 ... ( |_ ` t ) )' % PSET('Y', 't'))], '%s e. Fin' % PSET('Y', 't')),
                        cpcc(w, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't')), 'p', psmem(w, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't')), 'p', w.s([], 'simpr', '( ( %s /\\ p e. %s ) -> p e. %s )' % (Ay, PSET('Y', 't'), PSET('Y', 't'))), 'Y', 't')['pn'],
                             lift(w, nxh, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't'))), lift(w, tr, '( %s /\\ p e. %s )' % (Ay, PSET('Y', 't'))))], '%s e. CC' % PWt)
    bm = d('syl3anc', [d('syl', [f2i, w.inst('iblmbf')], '%s e. MblFn' % F2), g2i, ex, w.inst('bddmulibl')], '( %s oF x. %s ) e. L^1' % (F2, G2))
    # the product is | S |^2 / u
    q2 = dy('divcld', [dy('cjcld', [pwc], '( * ` %s ) e. CC' % PWt), tc2, tn2], '( ( * ` %s ) / t ) e. CC' % PWt)
    of = d('offval2', [d('ovexd', [], '%s e. _V' % YZ), pwc, q2, d('eqidd', [], '%s = %s' % (F2, F2)), d('eqidd', [], '%s = %s' % (G2, G2))],
           '( %s oF x. %s ) = ( t e. %s |-> ( %s x. ( ( * ` %s ) / t ) ) )' % (F2, G2, YZ, PWt, PWt))
    av = dy('syl', [pwc, w.inst('absvalsq')], '( ( abs ` %s ) ^ 2 ) = ( %s x. ( * ` %s ) )' % (PWt, PWt, PWt))
    pe = dy('eqtr4d', [dy('divassd', [pwc, dy('cjcld', [pwc], '( * ` %s ) e. CC' % PWt), tc2, tn2], '( ( %s x. ( * ` %s ) ) / t ) = ( %s x. ( ( * ` %s ) / t ) )' % (PWt, PWt, PWt, PWt)),
                       dy('oveq1d', [av], '( ( ( abs ` %s ) ^ 2 ) / t ) = ( ( %s x. ( * ` %s ) ) / t )' % (PWt, PWt, PWt))] if False else
            [dy('oveq1d', [av], '( ( ( abs ` %s ) ^ 2 ) / t ) = ( ( %s x. ( * ` %s ) ) / t )' % (PWt, PWt, PWt)),
             dy('divassd', [pwc, dy('cjcld', [pwc], '( * ` %s ) e. CC' % PWt), tc2, tn2], '( ( %s x. ( * ` %s ) ) / t ) = ( %s x. ( ( * ` %s ) / t ) )' % (PWt, PWt, PWt, PWt))], 'T.') if False else \
        dy('eqtrd', [dy('oveq1d', [av], '( ( ( abs ` %s ) ^ 2 ) / t ) = ( ( %s x. ( * ` %s ) ) / t )' % (PWt, PWt, PWt)),
                     dy('divassd', [pwc, dy('cjcld', [pwc], '( * ` %s ) e. CC' % PWt), tc2, tn2], '( ( %s x. ( * ` %s ) ) / t ) = ( %s x. ( ( * ` %s ) / t ) )' % (PWt, PWt, PWt, PWt))],
           '( ( ( abs ` %s ) ^ 2 ) / t ) = ( %s x. ( ( * ` %s ) / t ) )' % (PWt, PWt, PWt))
    TG = '( t e. %s |-> ( ( ( abs ` %s ) ^ 2 ) / t ) )' % (YZ, PWt)
    tg = d('eqtr4d', [d('mpteq2dva', [pe], '%s = ( t e. %s |-> ( %s x. ( ( * ` %s ) / t ) ) )' % (TG, YZ, PWt, PWt)), of], '%s = ( %s oF x. %s )' % (TG, F2, G2))
    tgi = d('eqeltrd', [tg, bm], '%s e. L^1' % TG)
    # rename t -> u
    TGu = '( u e. %s |-> ( ( ( abs ` %s ) ^ 2 ) / u ) )' % (YZ, PWS('T', 'Y', 'u'))
    cb = w.s([w.s([w.s([w.s([pwscong(w, 't', 'u')], 'fveq2d', '( t = u -> ( abs ` %s ) = ( abs ` %s ) )' % (PWt, PWS('T', 'Y', 'u')))], 'oveq1d',
                          '( t = u -> ( ( abs ` %s ) ^ 2 ) = ( ( abs ` %s ) ^ 2 ) )' % (PWt, PWS('T', 'Y', 'u'))), w.s([], 'id', '( t = u -> t = u )')], 'oveq12d',
                    '( t = u -> ( ( ( abs ` %s ) ^ 2 ) / t ) = ( ( ( abs ` %s ) ^ 2 ) / u ) )' % (PWt, PWS('T', 'Y', 'u')))], 'cbvmptv', '%s = %s' % (TG, TGu))
    fin = d('eqeltrrd', [w.s([cb], 'a1i', '( %s -> %s = %s )' % (A0, TG, TGu)), tgi], '%s e. L^1' % TGu)
    w.qed([fin], 'idi', S['kd2ibl'])
    return only_run(w, only)


if __name__ == '__main__':
    gen_ind()
    gen_log()
    gen_amx()
    gen_am()
    gen_abel()
    gen_ibl()
