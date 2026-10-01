"""Sortie LD2, section 6 part 1: the real lemmas, the weights and their integrals, Cauchy-Schwarz
(ld2gam ld2wsq ld2wlin ld2wtcn ld2rribl ld2efitg ld2wint ld2cs).
Run: MM_DB=sorties/ld2.mm MM_ENGINE=mmatch python3 tools/gen/ld2_b.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ld2lib import *

only = sys.argv[1:]
want = lambda l: not only or l in only
IM = '( Im ` W )'; RE = '( Re ` W )'
EIM = '( exp ` -u ( abs ` %s ) )' % IM


def rrss(w, A):
    return a1(w, A, 'ax-resscn', 'RR C_ CC')


def inst_forall(w, A, step, var, body_, val, valin):
    """( A -> body[var := val] ) from step ( A -> A. var e. CC body ) and valin ( A -> val e. CC )"""
    cg, new = w.wcongr(body_, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    return w.s([cg, step, valin], 'rspcdva', '( %s -> %s )' % (A, new)), new


def ld2gam():
    w = W('ld2gam', 'Lean ` hGamma ` of ` norm_ectrInt_half_le ` : on the half line ` -1/2 <_ Re w <_ -7/25 ` , ` abs Gamma ( w ) <_ 12000 e ^ -abs Im w ` from ` Gamma ( w + 1 ) = w Gamma ( w ) ` (~ gamp1 ), Z5d\'s ~ z5dgam ( ` abs Im >_ 1/2 ` ) and Z6a\'s ~ z6gam1632 ( ` abs Im < 1/2 ` , ` e ^ ( -1/2 ) >_ 1/2 ` ); ` ( 25 / 7 ) 3264 < 12000 ` .')
    A = ante('ld2gam'); P = parts(w, A)
    wc = P['W e. CC']; lo = P['-u ( 1 / 2 ) <_ %s' % RE]; hi = P['%s <_ -u ( 7 / ; 2 5 )' % RE]
    c = Closure(w, A, {'W': ('CC', wc)})
    c.leaf(RE, 'RR', dst(w, A, [wc], 'recld', '%s e. RR' % RE)); c.leaf(IM, 'RR', dst(w, A, [wc], 'imcld', '%s e. RR' % IM))
    AI = '( abs ` %s )' % IM
    c.leaf(AI, 'RR', c.mem(AI, 'RR')); c.leaf(AI, 'ge0', c.ge0(AI))
    c.leaf(EIM, 'RR+', dst(w, A, [c.mem('-u %s' % AI, 'RR')], 'rpefcld', '%s e. RR+' % EIM))
    # W is not an integer: W e. DG
    Az = '( %s /\\ W e. ZZ )' % A
    wz = w.s([], 'simpr', '( %s -> W e. ZZ )' % Az)
    wr = ap(w, Az, 'zre', [wz], 'W e. RR')
    rw = ap(w, Az, 'rere', [wr], '%s = W' % RE)
    cz = Closure(w, Az, {'W': ('RR', wr)})
    l1 = dst(w, Az, [lift(w, lo, Az), eqc(w, Az, rw)], 'breqtrrd', '-u ( 1 / 2 ) <_ W')
    l2 = dst(w, Az, [rw, lift(w, hi, Az)], 'eqbrtrrd', 'W <_ -u ( 7 / ; 2 5 )')
    m1 = linarith(w, Az, [l1], '-u 1 < W', closure=cz)
    m2 = linarith(w, Az, [l2], 'W < ( -u 1 + 1 )', closure=cz)
    nz = ap(w, Az, 'btwnnz', [J(w, Az, a1(w, Az, 'neg1z', '-u 1 e. ZZ'), m1, m2)], '-. W e. ZZ')
    nzz = w.s([wz, nz], 'pm2.65da', '( %s -> -. W e. ZZ )' % A)
    ndif = dst(w, A, [nzz, a1(w, A, 'eldifi', '( W e. ( ZZ \\ NN ) -> W e. ZZ )')], 'mtod', '-. W e. ( ZZ \\ NN )')
    wdg = dst(w, A, [wc, ndif], 'eldifd', 'W e. %s' % DG)
    # Gamma ( W + 1 ) = Gamma ( W ) W
    G0 = '( _G ` W )'; G1 = '( _G ` ( W + 1 ) )'
    gp = ap(w, A, 'gamp1', [wdg], '%s = ( %s x. W )' % (G1, G0))
    g0c = ap(w, A, 'gamcl', [wdg], '%s e. CC' % G0)
    c.leaf(G0, 'CC', g0c)
    c.leaf(G1, 'CC', dst(w, A, [gp, c.mem('( %s x. W )' % G0, 'CC')], 'eqeltrd', '%s e. CC' % G1))
    ag = dst(w, A, [g0c, wc], 'absmuld', '( abs ` ( %s x. W ) ) = ( ( abs ` %s ) x. ( abs ` W ) )' % (G0, G0))
    g1e = eqt(w, A, dst(w, A, [gp], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. W ) )' % (G1, G0)), ag)
    AG0 = '( abs ` %s )' % G0; AG1 = '( abs ` %s )' % G1; AW = '( abs ` W )'
    c.leaf(AG0, 'RR', c.mem(AG0, 'RR')); c.leaf(AG0, 'ge0', c.ge0(AG0)); c.leaf(AW, 'RR', c.mem(AW, 'RR'))
    # abs W >_ 7/25
    are = ap(w, A, 'absrele', [wc], '( abs ` %s ) <_ %s' % (RE, AW))
    re0 = linarith(w, A, [hi], '%s <_ 0' % RE, closure=c)
    an = ap(w, A, 'absnid', [J(w, A, c.mem(RE, 'RR'), re0)], '( abs ` %s ) = -u %s' % (RE, RE))
    ARE = '( abs ` %s )' % RE
    c.leaf(ARE, 'RR', c.mem(ARE, 'RR'))
    n1 = linarith(w, A, [hi], '( 7 / ; 2 5 ) <_ -u %s' % RE, closure=c)
    n2 = dst(w, A, [n1, eqc(w, A, an)], 'breqtrd', '( 7 / ; 2 5 ) <_ %s' % ARE)
    aw = dst(w, A, [c.mem('( 7 / ; 2 5 )', 'RR'), c.mem(ARE, 'RR'), c.mem(AW, 'RR'), n2, are], 'letrd', '( 7 / ; 2 5 ) <_ %s' % AW)
    p1 = dst(w, A, [c.mem('( 7 / ; 2 5 )', 'RR'), c.mem(AW, 'RR'), c.mem(AG0, 'RR'), c.ge0(AG0), aw], 'lemul2ad', '( %s x. ( 7 / ; 2 5 ) ) <_ ( %s x. %s )' % (AG0, AG0, AW))
    p2 = dst(w, A, [p1, eqc(w, A, g1e)], 'breqtrd', '( %s x. ( 7 / ; 2 5 ) ) <_ %s' % (AG0, AG1))
    # Gamma ( W + 1 ): 0 <_ Re <_ 1, 1/100 <_ Re <_ 3
    W1 = '( W + 1 )'
    w1c = c.mem(W1, 'CC')
    re1 = dst(w, A, [wc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'readdd', '( Re ` %s ) = ( %s + ( Re ` 1 ) )' % (W1, RE))
    re1b = eqt(w, A, re1, dst(w, A, [a1(w, A, 're1', '( Re ` 1 ) = 1')], 'oveq2d', '( %s + ( Re ` 1 ) ) = ( %s + 1 )' % (RE, RE)))
    im1 = dst(w, A, [wc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'imaddd', '( Im ` %s ) = ( %s + ( Im ` 1 ) )' % (W1, IM))
    im1b = eqt(w, A, im1, eqt(w, A, dst(w, A, [a1(w, A, 'im1', '( Im ` 1 ) = 0')], 'oveq2d', '( %s + ( Im ` 1 ) ) = ( %s + 0 )' % (IM, IM)), dst(w, A, [c.mem(IM, 'CC')], 'addridd', '( %s + 0 ) = %s' % (IM, IM))))
    RE1 = '( Re ` %s )' % W1
    c.leaf(RE1, 'RR', c.mem(RE1, 'RR'))
    r0 = dst(w, A, [linarith(w, A, [lo], '0 <_ ( %s + 1 )' % RE, closure=c), re1b], 'breqtrrd', '0 <_ %s' % RE1)
    r1 = dst(w, A, [re1b, linarith(w, A, [hi], '( %s + 1 ) <_ 1' % RE, closure=c)], 'eqbrtrd', '%s <_ 1' % RE1)
    rlo = dst(w, A, [linarith(w, A, [lo], '( 1 / ; ; 1 0 0 ) <_ ( %s + 1 )' % RE, closure=c), re1b], 'breqtrrd', '( 1 / ; ; 1 0 0 ) <_ %s' % RE1)
    rhi = dst(w, A, [re1b, linarith(w, A, [hi], '( %s + 1 ) <_ 3' % RE, closure=c)], 'eqbrtrd', '%s <_ 3' % RE1)
    aim1 = dst(w, A, [im1b], 'fveq2d', '( abs ` ( Im ` %s ) ) = %s' % (W1, AI))
    B = '( ; ; ; 3 2 6 4 x. %s )' % EIM
    c.leaf(AG1, 'RR', c.mem(AG1, 'RR'))
    # case abs Im W >_ 1/2
    A1 = '( %s /\\ ( 1 / 2 ) <_ %s )' % (A, AI)
    h1 = w.s([], 'simpr', '( %s -> ( 1 / 2 ) <_ %s )' % (A1, AI))
    h1b = dst(w, A1, [h1, lift(w, aim1, A1)], 'breqtrrd', '( 1 / 2 ) <_ ( abs ` ( Im ` %s ) )' % W1)
    zg = ap(w, A1, 'z5dgam', [J(w, A1, lift(w, w1c, A1), J(w, A1, lift(w, r0, A1), lift(w, r1, A1), h1b))], '%s <_ ( ; 6 0 x. ( exp ` -u ( abs ` ( Im ` %s ) ) ) )' % (AG1, W1))
    zg2 = dst(w, A1, [zg, dst(w, A1, [dst(w, A1, [dst(w, A1, [lift(w, aim1, A1)], 'negeqd', '-u ( abs ` ( Im ` %s ) ) = -u %s' % (W1, AI))], 'fveq2d', '( exp ` -u ( abs ` ( Im ` %s ) ) ) = %s' % (W1, EIM))], 'oveq2d',
                                       '( ; 6 0 x. ( exp ` -u ( abs ` ( Im ` %s ) ) ) ) = ( ; 6 0 x. %s )' % (W1, EIM))], 'breqtrd', '%s <_ ( ; 6 0 x. %s )' % (AG1, EIM))
    c1 = Closure(w, A1, {AG1: ('RR', lift(w, c.mem(AG1, 'RR'), A1)), EIM: ('RR+', lift(w, c.mem(EIM, 'RR+'), A1))})
    c1.atom(AG1); c1.atom(EIM)
    k1 = linarith(w, A1, [zg2, c1.ge0(EIM)], '%s <_ %s' % (AG1, B), closure=c1)
    # case abs Im W < 1/2
    A2 = '( %s /\\ -. ( 1 / 2 ) <_ %s )' % (A, AI)
    nl = w.s([], 'simpr', '( %s -> -. ( 1 / 2 ) <_ %s )' % (A2, AI))
    c2 = Closure(w, A2, {AG1: ('RR', lift(w, c.mem(AG1, 'RR'), A2)), EIM: ('RR+', lift(w, c.mem(EIM, 'RR+'), A2)), AI: [('RR', lift(w, c.mem(AI, 'RR'), A2)), ('ge0', lift(w, c.ge0(AI), A2))]})
    c2.atom(AG1); c2.atom(EIM); c2.atom(AI)
    lt = dst(w, A2, [nl, dst(w, A2, [c2.mem(AI, 'RR'), c2.mem('( 1 / 2 )', 'RR')], 'ltnled', '( %s < ( 1 / 2 ) <-> -. ( 1 / 2 ) <_ %s )' % (AI, AI))], 'mpbird', '%s < ( 1 / 2 )' % AI)
    g16 = w.s([], 'z6gam1632', Z6.GAMH1632)
    body_ = Z6.GAMH1632[len('A. d e. CC '):]
    ins, new = inst_forall(w, A2, w.s([g16], 'a1i', '( %s -> %s )' % (A2, Z6.GAMH1632)), 'd', body_, W1, lift(w, w1c, A2))
    bnd = dst(w, A2, [J(w, A2, lift(w, rlo, A2), lift(w, rhi, A2)), ins], 'mpd', split_imp(new)[1])
    E2 = '( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 2 ) )' % W1
    AI1 = '( abs ` ( Im ` %s ) )' % W1
    c2.leaf(AI1, 'RR', lift(w, c.mem(AI1, 'RR'), A2)); c2.leaf(AI1, 'ge0', lift(w, c.ge0(AI1), A2))
    e2le = ap(w, A2, 'cxplea', [J(w, A2, c2.mem('2', 'RR'), a1(w, A2, '1le2', '1 <_ 2')), J(w, A2, c2.mem('-u ( %s / 2 )' % AI1, 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A2)), linarith(w, A2, [c2.ge0(AI1)], '-u ( %s / 2 ) <_ 0' % AI1, closure=c2)],
               '%s <_ ( 2 ^c 0 )' % E2)
    e2le1 = dst(w, A2, [e2le, ap(w, A2, 'cxp0', [c2.mem('2', 'CC')], '( 2 ^c 0 ) = 1')], 'breqtrd', '%s <_ 1' % E2)
    c2.leaf(E2, 'RR', c2.mem(E2, 'RR')); c2.leaf(E2, 'ge0', c2.ge0(E2))
    b1 = linarith(w, A2, [bnd, e2le1], '%s <_ ; ; ; 1 6 3 2' % AG1, closure=c2)
    # e ^ -abs Im W >_ 1/2
    l2 = a1(w, A2, 'z5dlog2', '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )')
    c2.leaf('( log ` 2 )', 'RR', c2.mem('( log ` 2 )', 'RR'))
    hl = linarith(w, A2, [l2], '( 1 / 2 ) <_ ( log ` 2 )', closure=c2)
    ef1 = dst(w, A2, [hl, ap(w, A2, 'efle', [c2.mem('( 1 / 2 )', 'RR'), c2.mem('( log ` 2 )', 'RR')], '( ( 1 / 2 ) <_ ( log ` 2 ) <-> ( exp ` ( 1 / 2 ) ) <_ ( exp ` ( log ` 2 ) ) )')], 'mpbid', '( exp ` ( 1 / 2 ) ) <_ ( exp ` ( log ` 2 ) )')
    ef2 = dst(w, A2, [ef1, ap(w, A2, 'reeflog', [c2.mem('2', 'RR+')], '( exp ` ( log ` 2 ) ) = 2')], 'breqtrd', '( exp ` ( 1 / 2 ) ) <_ 2')
    EH = '( exp ` ( 1 / 2 ) )'
    c2.leaf(EH, 'RR+', dst(w, A2, [c2.mem('( 1 / 2 )', 'RR')], 'rpefcld', '%s e. RR+' % EH))
    lr = ap(w, A2, 'lerec', [J(w, A2, c2.mem(EH, 'RR'), c2.gt0(EH)), J(w, A2, c2.mem('2', 'RR'), c2.gt0('2'))], '( %s <_ 2 <-> ( 1 / 2 ) <_ ( 1 / %s ) )' % (EH, EH))
    r2 = dst(w, A2, [ef2, lr], 'mpbid', '( 1 / 2 ) <_ ( 1 / %s )' % EH)
    en = ap(w, A2, 'efneg', [c2.mem('( 1 / 2 )', 'CC')], '( exp ` -u ( 1 / 2 ) ) = ( 1 / %s )' % EH)
    r3 = dst(w, A2, [r2, en], 'breqtrrd', '( 1 / 2 ) <_ ( exp ` -u ( 1 / 2 ) )')
    mle = linarith(w, A2, [lt], '-u ( 1 / 2 ) <_ -u %s' % AI, closure=c2)
    ef3 = dst(w, A2, [mle, ap(w, A2, 'efle', [c2.mem('-u ( 1 / 2 )', 'RR'), c2.mem('-u %s' % AI, 'RR')], '( -u ( 1 / 2 ) <_ -u %s <-> ( exp ` -u ( 1 / 2 ) ) <_ %s )' % (AI, EIM))], 'mpbid', '( exp ` -u ( 1 / 2 ) ) <_ %s' % EIM)
    c2.leaf('( exp ` -u ( 1 / 2 ) )', 'RR', c2.mem('( exp ` -u ( 1 / 2 ) )', 'RR'))
    k2 = linarith(w, A2, [b1, r3, ef3], '%s <_ %s' % (AG1, B), closure=c2)
    kb = w.s([k1, k2], 'pm2.61dan', '( %s -> %s <_ %s )' % (A, AG1, B))
    c.leaf(AG1, 'RR', c.mem(AG1, 'RR'))
    linarith(w, A, [p2, kb, c.ge0(EIM)], '%s <_ ( %s x. %s )' % (AG0, GAMC, EIM), closure=c)
    return fin(w)


def ld2wsq():
    w = W('ld2wsq', 'Lean ` weight_sq_le ` : ` ( 1 + x ) ^ 2 e ^ -x <_ 8 e ^ -( x / 2 ) ` for ` x >_ 0 ` (~ efge1p2 at ` x / 2 ` , ~ efadd ).')
    A = ante('ld2wsq'); P = parts(w, A); xr = P['X e. RR']; x0 = P['0 <_ X']
    c = Closure(w, A, {'X': [('RR', xr), ('ge0', x0)]})
    H = '( X / 2 )'
    ef = ap(w, A, 'efge1p2', [J(w, A, c.mem(H, 'RR'), c.ge0(H))], '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ ( exp ` %s )' % (H, H, H))
    EH = '( exp ` %s )' % H; EX = '( exp ` -u X )'; EM = '( exp ` -u ( ( 1 / 2 ) x. X ) )'
    for e_ in (EH, EX, EM):
        c.leaf(e_, 'RR+', dst(w, A, [c.mem(e_[len('( exp ` '):-2], 'RR')], 'rpefcld', '%s e. RR+' % e_))
    sq = ringeqp(w, A, '( ( 1 + X ) ^ 2 )', '( ( 1 + ( 2 x. X ) ) + ( X x. X ) )', c)
    sq2 = ringeqp(w, A, '( 8 x. ( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) )' % (H, H), '( ( 8 + ( 4 x. X ) ) + ( X x. X ) )', c)
    c.atom('( X x. X )'); c.leaf('( X x. X )', 'RR', c.mem('( X x. X )', 'RR'))
    b1 = linarith(w, A, [sq, sq2, ef, x0], '( ( 1 + X ) ^ 2 ) <_ ( 8 x. %s )' % EH, closure=c)
    m1 = dst(w, A, [c.mem('( ( 1 + X ) ^ 2 )', 'RR'), c.mem('( 8 x. %s )' % EH, 'RR'), c.mem(EX, 'RR'), c.ge0(EX), b1], 'lemul1ad', '( ( ( 1 + X ) ^ 2 ) x. %s ) <_ ( ( 8 x. %s ) x. %s )' % (EX, EH, EX))
    ea = ap(w, A, 'efadd', [c.mem(H, 'CC'), c.mem('-u X', 'CC')], '( exp ` ( %s + -u X ) ) = ( %s x. %s )' % (H, EH, EX))
    eq = dst(w, A, [ringeq(w, A, '( %s + -u X )' % H, '-u ( ( 1 / 2 ) x. X )', c)], 'fveq2d', '( exp ` ( %s + -u X ) ) = %s' % (H, EM))
    pr = eqt(w, A, eqc(w, A, ea), eq)
    r1 = eqt(w, A, dst(w, A, [c.mem('8', 'CC'), c.mem(EH, 'CC'), c.mem(EX, 'CC')], 'mulassd', '( ( 8 x. %s ) x. %s ) = ( 8 x. ( %s x. %s ) )' % (EH, EX, EH, EX)), dst(w, A, [pr], 'oveq2d', '( 8 x. ( %s x. %s ) ) = ( 8 x. %s )' % (EH, EX, EM)))
    dst(w, A, [m1, r1], 'breqtrd', '( ( ( 1 + X ) ^ 2 ) x. %s ) <_ ( 8 x. %s )' % (EX, EM))
    return fin(w)


def ld2wlin():
    w = W('ld2wlin', 'Lean ` weight_lin_le ` : ` ( 3 + x ) e ^ -( x / 2 ) <_ 4 e ^ -( x / 4 ) ` for ` x >_ 0 ` (~ bvefge1p at ` x / 4 ` , ~ efadd ).')
    A = ante('ld2wlin'); P = parts(w, A); xr = P['X e. RR']; x0 = P['0 <_ X']
    c = Closure(w, A, {'X': [('RR', xr), ('ge0', x0)]})
    Q = '( X / 4 )'
    ef = ap(w, A, 'bvefge1p', [J(w, A, c.mem(Q, 'RR'), c.ge0(Q))], '( 1 + %s ) <_ ( exp ` %s )' % (Q, Q))
    EQ = '( exp ` %s )' % Q; EH = '( exp ` -u ( ( 1 / 2 ) x. X ) )'; EF = '( exp ` -u ( ( 1 / 4 ) x. X ) )'
    for e_ in (EQ, EH, EF):
        c.leaf(e_, 'RR+', dst(w, A, [c.mem(e_[len('( exp ` '):-2], 'RR')], 'rpefcld', '%s e. RR+' % e_))
    b1 = linarith(w, A, [ef], '( 3 + X ) <_ ( 4 x. %s )' % EQ, closure=c)
    m1 = dst(w, A, [c.mem('( 3 + X )', 'RR'), c.mem('( 4 x. %s )' % EQ, 'RR'), c.mem(EH, 'RR'), c.ge0(EH), b1], 'lemul1ad', '( ( 3 + X ) x. %s ) <_ ( ( 4 x. %s ) x. %s )' % (EH, EQ, EH))
    ea = ap(w, A, 'efadd', [c.mem(Q, 'CC'), c.mem('-u ( ( 1 / 2 ) x. X )', 'CC')], '( exp ` ( %s + -u ( ( 1 / 2 ) x. X ) ) ) = ( %s x. %s )' % (Q, EQ, EH))
    eq = dst(w, A, [ringeq(w, A, '( %s + -u ( ( 1 / 2 ) x. X ) )' % Q, '-u ( ( 1 / 4 ) x. X )', c)], 'fveq2d', '( exp ` ( %s + -u ( ( 1 / 2 ) x. X ) ) ) = %s' % (Q, EF))
    pr = eqt(w, A, eqc(w, A, ea), eq)
    r1 = eqt(w, A, dst(w, A, [c.mem('4', 'CC'), c.mem(EQ, 'CC'), c.mem(EH, 'CC')], 'mulassd', '( ( 4 x. %s ) x. %s ) = ( 4 x. ( %s x. %s ) )' % (EQ, EH, EQ, EH)), dst(w, A, [pr], 'oveq2d', '( 4 x. ( %s x. %s ) ) = ( 4 x. %s )' % (EQ, EH, EF)))
    dst(w, A, [m1, r1], 'breqtrd', '( ( 3 + X ) x. %s ) <_ ( 4 x. %s )' % (EH, EF))
    return fin(w)


def ld2wtcn():
    w = W('ld2wtcn', 'The weight ` u |-> e ^ -( A abs u ) ` is continuous on ` RR ` (~ efcn , ~ abscncf , ~ mulcncf ).')
    A = 'A e. RR'
    ar = w.s([], 'id', '( %s -> %s )' % (A, A))
    c0 = Closure(w, A, {'A': ('RR', ar)})
    Au = '( %s /\\ u e. RR )' % A
    cv = Closure(w, Au, {'A': ('RR', lift(w, ar, Au)), 'u': ('RR', w.s([], 'simpr', '( %s -> u e. RR )' % Au))})
    cn = CN(w, A, 'u', 'RR', rrss(w, A), c0, cv)
    cn(WTA('A', 'u'))
    return fin(w)


def ld2rribl():
    w = W('ld2rribl', 'A mapping continuous on ` RR ` is integrable on every bounded open interval (~ rescncf , ~ cniccibl , ~ iblss ; Lean ` Integrable ` of the weighted mollifier on a truncation).')
    A = 'ph'
    h1, h2 = hyps(w, 'ld2rribl')
    ar = dst(w, A, [h1], 'simpld', 'A e. RR'); br = dst(w, A, [h1], 'simprd', 'B e. RR')
    ICC = '( A [,] B )'; IOO_ = '( A (,) B )'
    F = '( u e. RR |-> X )'; FI = '( u e. %s |-> X )' % ICC; FO = '( u e. %s |-> X )' % IOO_
    ss = ap(w, A, 'iccssre', [ar, br], '%s C_ RR' % ICC)
    rc = w.s([ss, a1(w, A, 'rescncf', '( %s C_ RR -> ( %s e. ( RR -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (ICC, F, F, ICC, ICC))], 'mpd', '( %s -> ( %s e. ( RR -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A, F, F, ICC, ICC))
    rc2 = w.s([h2, rc], 'mpd', '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A, F, ICC, ICC))
    rm = ap(w, A, 'resmpt', [ss], '( %s |` %s ) = %s' % (F, ICC, FI))
    ci = dst(w, A, [rm, rc2], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (FI, ICC))
    ib = ap(w, A, 'cniccibl', [ar, br, ci], '%s e. L^1' % FI)
    ff = ap(w, A, 'cncff', [h2], '%s : RR --> CC' % F)
    fm = w.s([], 'eqid', '%s = %s' % (F, F))
    al = w.s([ff, w.s([fm], 'fmpt', '( A. u e. RR X e. CC <-> %s : RR --> CC )' % F)], 'sylibr', '( %s -> A. u e. RR X e. CC )' % A)
    Ai = '( %s /\\ u e. %s )' % (A, ICC)
    ur = dst(w, Ai, [lift(w, ss, Ai), w.s([], 'simpr', '( %s -> u e. %s )' % (Ai, ICC))], 'sseldd', 'u e. RR')
    xc = w.s([lift(w, al, Ai), ur, w.inst('rspa')], 'syl2anc', '( %s -> X e. CC )' % Ai)
    w.s([a1(w, A, 'ioossicc', '%s C_ %s' % (IOO_, ICC)), a1(w, A, 'ioombl', '%s e. dom vol' % IOO_), xc, ib], 'iblss', '( %s -> %s e. L^1 )' % (A, FO))
    return fin(w)


def dvexp_neg(w, A, c, Ax, cx):
    """( A -> ( RR _D ( x e. RR |-> ( exp ` -u ( A x. x ) ) ) ) = ( x e. RR |-> ( ( exp ` -u ( A x. x ) ) x. -u A ) ) ) for A e. RR (leaf of c);
    Ax = ( A /\\ x e. RR ), cx its closure"""
    rr = a1(w, A, 'reelprrecn', 'RR e. { RR , CC }'); cc = a1(w, A, 'cnelprrecn', 'CC e. { RR , CC }')
    did = w.s([rr], 'dvmptid', '( %s -> ( RR _D ( x e. RR |-> x ) ) = ( x e. RR |-> 1 ) )' % A)
    dm = w.s([rr, cx.mem('x', 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % Ax), did, c.mem('A', 'CC')], 'dvmptcmul', '( %s -> ( RR _D ( x e. RR |-> ( A x. x ) ) ) = ( x e. RR |-> ( A x. 1 ) ) )' % A)
    m1 = dst(w, Ax, [cx.mem('A', 'CC')], 'mulridd', '( A x. 1 ) = A')
    da = eqt(w, A, dm, dst(w, A, [m1], 'mpteq2dva', '( x e. RR |-> ( A x. 1 ) ) = ( x e. RR |-> A )'))
    dn = w.s([rr, cx.mem('( A x. x )', 'CC'), cx.mem('A', 'CC'), da], 'dvmptneg', '( %s -> ( RR _D ( x e. RR |-> -u ( A x. x ) ) ) = ( x e. RR |-> -u A ) )' % A)
    Ay = '( %s /\\ y e. CC )' % A
    cy = Closure(w, Ay, {'y': ('CC', w.s([], 'simpr', '( %s -> y e. CC )' % Ay))})
    ef = a1(w, A, 'eff', 'exp : CC --> CC')
    ee = dst(w, A, [ef], 'feqmptd', 'exp = ( y e. CC |-> ( exp ` y ) )')
    de = a1(w, A, 'dvef', '( CC _D exp ) = exp')
    x1 = dst(w, A, [ee], 'oveq2d', '( CC _D exp ) = ( CC _D ( y e. CC |-> ( exp ` y ) ) )')
    dc = eqt(w, A, eqt(w, A, eqc(w, A, x1), de), ee)
    e = w.s([], 'fveq2', '( y = -u ( A x. x ) -> ( exp ` y ) = ( exp ` -u ( A x. x ) ) )')
    E = '( exp ` -u ( A x. x ) )'
    co = w.s([rr, cc, cx.mem('-u ( A x. x )', 'CC'), cx.mem('-u A', 'CC'), cy.mem('( exp ` y )', 'CC'), cy.mem('( exp ` y )', 'CC'), dn, dc, e, e],
             'dvmptco', '( %s -> ( RR _D ( x e. RR |-> %s ) ) = ( x e. RR |-> ( %s x. -u A ) ) )' % (A, E, E))
    return co, E


def ld2efitg():
    w = W('ld2efitg', 'Lean ` integral_exp_neg_abs_mul ` (one side): ` S. ( 0 (,) B ) e ^ -( A u ) du = ( 1 - e ^ -( A B ) ) / A <_ 1 / A ` by the FTC (~ lsftc ) with the primitive ` -e ^ -( A u ) / A ` (~ dvmptco , ~ dvef ).')
    A = ante('ld2efitg'); P = parts(w, A); arp = P['A e. RR+']; br = P['B e. RR']; b0 = P['0 <_ B']
    c = Closure(w, A, {'A': ('RR+', arp), 'B': [('RR', br), ('ge0', b0)]})
    Ax = '( %s /\\ x e. RR )' % A
    cx = Closure(w, Ax, {'A': ('RR+', lift(w, arp, Ax)), 'x': ('RR', w.s([], 'simpr', '( %s -> x e. RR )' % Ax))})
    co, E = dvexp_neg(w, A, c, Ax, cx)
    K = '( -u 1 / A )'
    kc = c.mem(K, 'CC')
    rr = a1(w, A, 'reelprrecn', 'RR e. { RR , CC }')
    dF = w.s([rr, cx.mem(E, 'CC'), cx.mem('( %s x. -u A )' % E, 'CC'), co, kc], 'dvmptcmul', '( %s -> ( RR _D ( x e. RR |-> ( %s x. %s ) ) ) = ( x e. RR |-> ( %s x. ( %s x. -u A ) ) ) )' % (A, K, E, K, E))
    # K x. ( E x. -u A ) = E
    m1 = dst(w, Ax, [cx.mem(K, 'CC'), cx.mem(E, 'CC'), cx.mem('-u A', 'CC')], 'mul12d', '( %s x. ( %s x. -u A ) ) = ( %s x. ( %s x. -u A ) )' % (K, E, E, K))
    m2 = dst(w, Ax, [cx.mem(K, 'CC'), cx.mem('A', 'CC')], 'mulneg2d', '( %s x. -u A ) = -u ( %s x. A )' % (K, K))
    m3 = dst(w, Ax, [cx.mem('-u 1', 'CC'), cx.mem('A', 'CC'), cx.ne0('A')], 'divcan1d', '( %s x. A ) = -u 1' % K)
    m4 = eqt(w, Ax, m2, eqt(w, Ax, dst(w, Ax, [m3], 'negeqd', '-u ( %s x. A ) = -u -u 1' % K), a1(w, Ax, 'negneg1e1', '-u -u 1 = 1')))
    m5 = eqt(w, Ax, m1, eqt(w, Ax, dst(w, Ax, [m4], 'oveq2d', '( %s x. ( %s x. -u A ) ) = ( %s x. 1 )' % (E, K, E)), dst(w, Ax, [cx.mem(E, 'CC')], 'mulridd', '( %s x. 1 ) = %s' % (E, E))))
    F = '( x e. RR |-> ( %s x. %s ) )' % (K, E); G = '( x e. RR |-> %s )' % E
    dF2 = eqt(w, A, dF, dst(w, A, [m5], 'mpteq2dva', '( x e. RR |-> ( %s x. ( %s x. -u A ) ) ) = %s' % (K, E, G)))
    ff = dst(w, A, [cx.mem('( %s x. %s )' % (K, E), 'CC')], 'fmptd', '%s : RR --> CC' % F)
    cn = CN(w, A, 'x', 'RR', rrss(w, A), c, cx)
    gcn = cn(E)
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A)
    ftc = ap(w, A, 'lsftc', [J(w, A, z0, br, b0), J(w, A, ff, dF2, gcn)], '%s = ( ( %s ` B ) - ( %s ` 0 ) )' % (ITG(IOO('0', 'B'), '( %s ` u )' % G, 'u'), F, F))
    # the integrand
    Au = '( %s /\\ u e. %s )' % (A, IOO('0', 'B'))
    ur = ap(w, Au, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, IOO('0', 'B')))], 'u e. RR')
    cu = Closure(w, Au, {'A': ('RR+', lift(w, arp, Au)), 'u': ('RR', ur)})
    EU = '( exp ` -u ( A x. u ) )'
    gv = fvmd(w, Au, 'x', 'RR', E, 'u', ur, cu.mem(EU, 'CC'))
    ig = dst(w, A, [gv], 'itgeq2dv', '%s = %s' % (ITG(IOO('0', 'B'), '( %s ` u )' % G, 'u'), ITG(IOO('0', 'B'), EU, 'u')))
    # F at the ends
    EB = '( exp ` -u ( A x. B ) )'
    fB = fvmd(w, A, 'x', 'RR', '( %s x. %s )' % (K, E), 'B', br, c.mem('( %s x. %s )' % (K, EB), 'CC'))
    f0 = fvmd(w, A, 'x', 'RR', '( %s x. %s )' % (K, E), '0', z0, c.mem('( %s x. ( exp ` -u ( A x. 0 ) ) )' % K, 'CC'))
    e0 = eqt(w, A, dst(w, A, [dst(w, A, [dst(w, A, [c.mem('A', 'CC')], 'mul01d', '( A x. 0 ) = 0')], 'negeqd', '-u ( A x. 0 ) = -u 0')], 'fveq2d', '( exp ` -u ( A x. 0 ) ) = ( exp ` -u 0 )'),
             eqt(w, A, dst(w, A, [a1(w, A, 'neg0', '-u 0 = 0')], 'fveq2d', '( exp ` -u 0 ) = ( exp ` 0 )'), a1(w, A, 'ef0', '( exp ` 0 ) = 1')))
    f0b = eqt(w, A, f0, eqt(w, A, dst(w, A, [e0], 'oveq2d', '( %s x. ( exp ` -u ( A x. 0 ) ) ) = ( %s x. 1 )' % (K, K)), dst(w, A, [kc], 'mulridd', '( %s x. 1 ) = %s' % (K, K))))
    val = eqt(w, A, eqc(w, A, ig), eqt(w, A, ftc, dst(w, A, [fB, f0b], 'oveq12d', '( ( %s ` B ) - ( %s ` 0 ) ) = ( ( %s x. %s ) - %s )' % (F, F, K, EB, K))))
    R = '( 1 / A )'
    dn = dst(w, A, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A), c.mem('A', 'CC'), c.ne0('A')], 'divnegd', '-u %s = %s' % (R, K))
    c.leaf(R, 'RR+', c.mem(R, 'RR+')); c.leaf(EB, 'RR+', dst(w, A, [c.mem('-u ( A x. B )', 'RR')], 'rpefcld', '%s e. RR+' % EB))
    val2 = eqt(w, A, val, dst(w, A, [dst(w, A, [eqc(w, A, dn)], 'oveq1d', '( %s x. %s ) = ( -u %s x. %s )' % (K, EB, R, EB)), eqc(w, A, dn)], 'oveq12d', '( ( %s x. %s ) - %s ) = ( ( -u %s x. %s ) - -u %s )' % (K, EB, K, R, EB, R)))
    bnd = nlinarith(w, A, [c.ge0(R), c.ge0(EB)], '( ( -u %s x. %s ) - -u %s ) <_ %s' % (R, EB, R, R), closure=c)
    dst(w, A, [val2, bnd], 'eqbrtrd', '%s <_ %s' % (ITG(IOO('0', 'B'), EU, 'u'), R))
    return fin(w)


def ld2wint():
    w = W('ld2wint', 'Lean ` integral_exp_neg_abs_mul ` : ` S. ( -H (,) H ) e ^ -( A abs u ) du <_ 2 / A ` (the split at ` 0 ` ~ itgsplitioo , MV\'s reflection ~ mvrefl , ~ ld2efitg on each side).')
    A = ante('ld2wint'); P = parts(w, A); arp = P['A e. RR+']; hrp = P['H e. RR+']
    c = Closure(w, A, {'A': ('RR+', arp), 'H': ('RR+', hrp)})
    WU = WTA('A', 'u'); WX = WTA('A', 'x')
    F = '( x e. RR |-> %s )' % WX
    cnu = ap(w, A, 'ld2wtcn', [c.mem('A', 'RR')], '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % WU)
    cg, _ = w.congr(WU, {'u': 'x'}, 'u = x', {'u': w.s([], 'id', '( u = x -> u = x )')})
    me = w.s([cg], 'cbvmptv', '( u e. RR |-> %s ) = %s' % (WU, F))
    cnx = dst(w, A, [w.s([me], 'a1i', '( %s -> ( u e. RR |-> %s ) = %s )' % (A, WU, F)), cnu], 'eqeltrrd', '%s e. ( RR -cn-> CC )' % F)
    hr = c.mem('H', 'RR'); nhr = c.mem('-u H', 'RR')
    IL = IOO('-u H', '0'); IR = IOO('0', 'H'); IH = IOH('H')
    ibl = w.s([J(w, A, nhr, w.s([], '0red', '( %s -> 0 e. RR )' % A)), cnu], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, IL, WU))
    ibr = w.s([J(w, A, w.s([], '0red', '( %s -> 0 e. RR )' % A), hr), cnu], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, IR, WU))
    Au = '( %s /\\ u e. %s )' % (A, IH)
    ur = ap(w, Au, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, IH))], 'u e. RR')
    cu = Closure(w, Au, {'A': ('RR+', lift(w, arp, Au)), 'u': ('RR', ur)})
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A)
    zin = dst(w, A, [J(w, A, nhr, hr), J(w, A, linarith(w, A, [c.gt0('H')], '-u H <_ 0', closure=c), c.ge0('H'))], 'jca', '( ( -u H e. RR /\\ H e. RR ) /\\ ( -u H <_ 0 /\\ 0 <_ H ) )')
    zic = dst(w, A, [J(w, A, z0, linarith(w, A, [c.gt0('H')], '-u H <_ 0', closure=c), c.ge0('H')), ap(w, A, 'elicc2', [nhr, hr], '( 0 e. ( -u H [,] H ) <-> ( 0 e. RR /\\ -u H <_ 0 /\\ 0 <_ H ) )')], 'mpbird', '0 e. ( -u H [,] H )')
    sp = w.s([nhr, hr, zic, cu.mem(WU, 'CC'), ibl, ibr], 'itgsplitioo', '( %s -> %s = ( %s + %s ) )' % (A, ITG(IH, WU, 'u'), ITG(IL, WU, 'u'), ITG(IR, WU, 'u')))
    # the right half
    Ar = '( %s /\\ u e. %s )' % (A, IR)
    urr = ap(w, Ar, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Ar, IR))], 'u e. RR')
    u0 = dst(w, Ar, [ap(w, Ar, 'eliooord', [w.s([], 'simpr', '( %s -> u e. %s )' % (Ar, IR))], '( 0 < u /\\ u < H )')], 'simpld', '0 < u')
    cr = Closure(w, Ar, {'A': ('RR+', lift(w, arp, Ar)), 'u': [('RR', urr), ('gt0', u0)]})
    ai = dst(w, Ar, [urr, cr.ge0('u')], 'absidd', '( abs ` u ) = u')
    EU = '( exp ` -u ( A x. u ) )'
    er = dst(w, Ar, [dst(w, Ar, [dst(w, Ar, [ai], 'oveq2d', '( A x. ( abs ` u ) ) = ( A x. u )')], 'negeqd', '-u ( A x. ( abs ` u ) ) = -u ( A x. u )')], 'fveq2d', '%s = %s' % (WU, EU))
    igr = dst(w, A, [er], 'itgeq2dv', '%s = %s' % (ITG(IR, WU, 'u'), ITG(IR, EU, 'u')))
    br = ap(w, A, 'ld2efitg', [arp, J(w, A, hr, c.ge0('H'))], '%s <_ ( 1 / A )' % ITG(IR, EU, 'u'))
    kr = dst(w, A, [igr, br], 'eqbrtrd', '%s <_ ( 1 / A )' % ITG(IR, WU, 'u'))
    # the left half by reflection
    rf = ap(w, A, 'mvrefl', [hrp, cnx], '%s = %s' % (ITG(IL, '( %s ` u )' % F, 'u'), ITG(IR, '( %s ` -u u )' % F, 'u')))
    Al = '( %s /\\ u e. %s )' % (A, IL)
    ul = ap(w, Al, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Al, IL))], 'u e. RR')
    cl_ = Closure(w, Al, {'A': ('RR+', lift(w, arp, Al)), 'u': ('RR', ul)})
    fvl = fvmd(w, Al, 'x', 'RR', WX, 'u', ul, cl_.mem(WU, 'CC'))
    igl = dst(w, A, [fvl], 'itgeq2dv', '%s = %s' % (ITG(IL, '( %s ` u )' % F, 'u'), ITG(IL, WU, 'u')))
    WNU = WTA('A', '-u u')
    fvr = fvmd(w, Ar, 'x', 'RR', WX, '-u u', cr.mem('-u u', 'RR'), cr.mem(WNU, 'CC'))
    an = dst(w, Ar, [cr.mem('u', 'CC')], 'absnegd', '( abs ` -u u ) = ( abs ` u )')
    er2 = dst(w, Ar, [dst(w, Ar, [dst(w, Ar, [eqt(w, Ar, an, ai)], 'oveq2d', '( A x. ( abs ` -u u ) ) = ( A x. u )')], 'negeqd', '-u ( A x. ( abs ` -u u ) ) = -u ( A x. u )')], 'fveq2d', '%s = %s' % (WNU, EU))
    igr2 = dst(w, A, [eqt(w, Ar, fvr, er2)], 'itgeq2dv', '%s = %s' % (ITG(IR, '( %s ` -u u )' % F, 'u'), ITG(IR, EU, 'u')))
    kl = dst(w, A, [eqt(w, A, eqc(w, A, igl), eqt(w, A, rf, igr2)), br], 'eqbrtrd', '%s <_ ( 1 / A )' % ITG(IL, WU, 'u'))
    # the sum
    R = '( 1 / A )'
    c.leaf(R, 'RR+', c.mem(R, 'RR+'))
    il = dst(w, A, [cl_.mem(WU, 'RR'), ibl], 'itgrecl', '%s e. RR' % ITG(IL, WU, 'u'))
    ir = dst(w, A, [cr.mem(WU, 'RR'), ibr], 'itgrecl', '%s e. RR' % ITG(IR, WU, 'u'))
    c.leaf(ITG(IL, WU, 'u'), 'RR', il); c.leaf(ITG(IR, WU, 'u'), 'RR', ir)
    dr = ap(w, A, 'divrec', [c.mem('2', 'CC'), c.mem('A', 'CC'), c.ne0('A')], '( 2 / A ) = ( 2 x. %s )' % R)
    s2 = linarith(w, A, [kl, kr, dr], '( %s + %s ) <_ ( 2 / A )' % (ITG(IL, WU, 'u'), ITG(IR, WU, 'u')), closure=c)
    dst(w, A, [sp, s2], 'eqbrtrd', '%s <_ ( 2 / A )' % ITG(IH, WU, 'u'))
    return fin(w)


def ld2cs():
    w = W('ld2cs', 'Lean ` key ` of ` sq_integral_weight_le ` , the weighted AM-GM inequality with free real constants ` X ` , ` M ` : ` 2 X M S. W Z <_ X ^ 2 S. W + M ^ 2 S. W Z ^ 2 ` for nonnegative integrable ` W ` , ` Z ` (pointwise ` 0 <_ ( X - M Z ) ^ 2 ` ; ~ itgle , ~ itgadd , ~ itgmulc2 ).')
    A = 'ph'
    h1, h2, h3, h4, h5, h6, h7 = hyps(w, 'ld2cs')
    I = IOO('A', 'B')
    Au = '( %s /\\ u e. %s )' % (A, I)
    wr = dst(w, Au, [h2], 'simpld', 'W e. RR'); w0 = dst(w, Au, [h2], 'simprd', '0 <_ W')
    zr = dst(w, Au, [h3], 'simpld', 'Z e. RR'); z0 = dst(w, Au, [h3], 'simprd', '0 <_ Z')
    xr = dst(w, A, [h7], 'simpld', 'X e. RR'); mr = dst(w, A, [h7], 'simprd', 'M e. RR')
    cu = Closure(w, Au, {'W': [('RR', wr), ('ge0', w0)], 'Z': [('RR', zr), ('ge0', z0)], 'X': ('RR', lift(w, xr, Au)), 'M': ('RR', lift(w, mr, Au))})
    cu.atom('W'); cu.atom('Z'); cu.atom('X'); cu.atom('M')
    c = Closure(w, A, {'X': ('RR', xr), 'M': ('RR', mr)})
    c.atom('X'); c.atom('M')
    # pointwise
    Q = '( X - ( M x. Z ) )'
    sq = dst(w, Au, [cu.mem(Q, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % Q)
    ex = ringeqp(w, Au, '( %s ^ 2 )' % Q, '( ( ( X ^ 2 ) - ( ( 2 x. ( X x. M ) ) x. Z ) ) + ( ( M ^ 2 ) x. ( Z ^ 2 ) ) )', cu)
    L1 = '( ( 2 x. ( X x. M ) ) x. Z )'; R1 = '( ( X ^ 2 ) + ( ( M ^ 2 ) x. ( Z ^ 2 ) ) )'
    pw = linarith(w, Au, [sq, ex], '%s <_ %s' % (L1, R1), closure=cu)
    mw = dst(w, Au, [cu.mem(L1, 'RR'), cu.mem(R1, 'RR'), wr, w0, pw], 'lemul2ad', '( W x. %s ) <_ ( W x. %s )' % (L1, R1))
    C2 = '( 2 x. ( X x. M ) )'
    LB = '( %s x. ( W x. Z ) )' % C2; RB = '( ( ( X ^ 2 ) x. W ) + ( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) ) )'
    e1 = ringeq(w, Au, '( W x. %s )' % L1, LB, cu); e2 = ringeq(w, Au, '( W x. %s )' % R1, RB, cu)
    pw2 = w.s([mw, e1, e2], '3brtr3d', '( %s -> %s <_ %s )' % (Au, LB, RB))
    # integrability
    c2c = c.mem(C2, 'CC'); x2c = c.mem('( X ^ 2 )', 'CC'); m2c = c.mem('( M ^ 2 )', 'CC')
    wzc = cu.mem('( W x. Z )', 'CC'); wc = cu.mem('W', 'CC'); wz2c = cu.mem('( W x. ( Z ^ 2 ) )', 'CC')
    ilb = w.s([c2c, wzc, h5], 'iblmulc2', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, LB))
    ia = w.s([x2c, wc, h4], 'iblmulc2', '( %s -> ( u e. %s |-> ( ( X ^ 2 ) x. W ) ) e. L^1 )' % (A, I))
    ib = w.s([m2c, wz2c, h6], 'iblmulc2', '( %s -> ( u e. %s |-> ( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) ) ) e. L^1 )' % (A, I))
    irb = w.s([cu.mem('( ( X ^ 2 ) x. W )', 'CC'), ia, cu.mem('( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) )', 'CC'), ib], 'ibladd', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, RB))
    il = w.s([ilb, irb, cu.mem(LB, 'RR'), cu.mem(RB, 'RR'), pw2], 'itgle', '( %s -> %s <_ %s )' % (A, ITG(I, LB, 'u'), ITG(I, RB, 'u')))
    # the integrals
    m0 = w.s([c2c, wzc, h5], 'itgmulc2', '( %s -> ( %s x. %s ) = %s )' % (A, C2, ITG(I, '( W x. Z )', 'u'), ITG(I, LB, 'u')))
    ad = w.s([cu.mem('( ( X ^ 2 ) x. W )', 'CC'), ia, cu.mem('( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) )', 'CC'), ib], 'itgadd',
             '( %s -> %s = ( %s + %s ) )' % (A, ITG(I, RB, 'u'), ITG(I, '( ( X ^ 2 ) x. W )', 'u'), ITG(I, '( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) )', 'u')))
    ma = w.s([x2c, wc, h4], 'itgmulc2', '( %s -> ( ( X ^ 2 ) x. %s ) = %s )' % (A, ITG(I, 'W', 'u'), ITG(I, '( ( X ^ 2 ) x. W )', 'u')))
    mb = w.s([m2c, wz2c, h6], 'itgmulc2', '( %s -> ( ( M ^ 2 ) x. %s ) = %s )' % (A, ITG(I, '( W x. ( Z ^ 2 ) )', 'u'), ITG(I, '( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) )', 'u')))
    rhs = eqt(w, A, ad, eqc(w, A, dst(w, A, [ma, mb], 'oveq12d', '( ( ( X ^ 2 ) x. %s ) + ( ( M ^ 2 ) x. %s ) ) = ( %s + %s )' % (ITG(I, 'W', 'u'), ITG(I, '( W x. ( Z ^ 2 ) )', 'u'), ITG(I, '( ( X ^ 2 ) x. W )', 'u'), ITG(I, '( ( M ^ 2 ) x. ( W x. ( Z ^ 2 ) ) )', 'u')))))
    w.s([il, m0, eqc(w, A, rhs)], '3brtr4d', '( %s -> ( %s x. %s ) <_ ( ( ( X ^ 2 ) x. %s ) + ( ( M ^ 2 ) x. %s ) ) )' % (A, C2, ITG(I, '( W x. Z )', 'u'), ITG(I, 'W', 'u'), ITG(I, '( W x. ( Z ^ 2 ) )', 'u')))
    return fin(w)


if __name__ == '__main__':
    for f in (ld2gam, ld2wsq, ld2wlin, ld2wtcn, ld2rribl, ld2efitg, ld2wint, ld2cs):
        if want(f.__name__):
            f()
