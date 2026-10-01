"""Sortie z4d, section C: the sieve side (lscopsift, lspwb and its lemmas)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
import lin
lin.FASTPATH = True
from lin import linarith, lineq, nlinarith
from z4dlib import STATEMENTS as S, HYPS, Q0S, SIFT, HPS, RHO, D4, H8, GW, WIF, LOGN, AX, PC, LZ, DB, ABS2
from z4d_a import mk, a1


def lscopsift():
    w = W('lscopsift', 'A number all of whose prime factors exceed Q is coprime to every D <_ Q '
          '(Lean coprime_of_minFac, with the sifting hypothesis in prime-divisor form).')
    IMP = '( p || N -> Q < p )'
    SN = 'A. p e. Prime %s' % IMP
    P0 = '( Q e. RR /\\ N e. NN /\\ D e. %s )' % Q0S
    DV = '( p || N /\\ p || D )'
    FL = '( |_ ` Q )'
    B = '( %s /\\ p e. Prime )' % P0
    BI = '( %s /\\ %s )' % (B, IMP)
    C = '( %s /\\ %s )' % (BI, DV)
    c = mk(w, C)
    b0 = w.s([w.s([], 'simpll', '( %s -> %s )' % (C, B))], 'simpld', '( %s -> %s )' % (C, P0))
    qr = c([b0], 'simp1d', 'Q e. RR')
    dfz = c([b0], 'simp3d', 'D e. %s' % Q0S)
    dnn = c([dfz, w.inst('elfznn')], 'syl', 'D e. NN')
    pp = c([w.s([], 'simpll', '( %s -> %s )' % (C, B))], 'simprd', 'p e. Prime')
    qp = c([c([], 'simprl', 'p || N'), c([], 'simplr', IMP)], 'mpd', 'Q < p')
    pz = c([pp, w.inst('prmz')], 'syl', 'p e. ZZ')
    pd = c([c([pz, dnn, w.inst('dvdsle')], 'syl2anc', '( p || D -> p <_ D )'), c([], 'simprr', 'p || D')], 'mpd', 'p <_ D')
    dfl = c([dfz, w.inst('elfzle2')], 'syl', 'D <_ %s' % FL)
    flq = c([qr, w.inst('flle')], 'syl', '%s <_ Q' % FL)
    flr = c([c([qr], 'flcld', '%s e. ZZ' % FL)], 'zred', '%s e. RR' % FL)
    lv = {'p': c([pz], 'zred', 'p e. RR'), 'D': c([dnn], 'nnred', 'D e. RR'), FL: flr, 'Q': qr}
    nq = linarith(w, C, [pd, dfl, flq], 'p <_ Q', leaves=lv)
    nqp = c([c([lv['p'], qr], 'lenltd', '( p <_ Q <-> -. Q < p )'), nq], 'mpbid', '-. Q < p')
    nd = w.s([qp, nqp], 'pm2.65da', '( %s -> -. %s )' % (BI, DV))
    ex = w.s([nd], 'ex', '( %s -> ( %s -> -. %s ) )' % (B, IMP, DV))
    ri = w.s([ex], 'ralimdva', '( %s -> ( %s -> A. p e. Prime -. %s ) )' % (P0, SN, DV))
    ne = w.s([ri, w.s([], 'ralnex', '( A. p e. Prime -. %s <-> -. E. p e. Prime %s )' % (DV, DV))], 'imbitrdi',
             '( %s -> ( %s -> -. E. p e. Prime %s ) )' % (P0, SN, DV))
    E0 = '( %s /\\ %s )' % (P0, SN)
    e = mk(w, E0)
    ne2 = w.s([ne], 'imp', '( %s -> -. E. p e. Prime %s )' % (E0, DV))
    ND = '( N e. NN /\\ D e. NN )'
    bi = w.s([w.s([], 'simpl', '( %s -> N e. NN )' % ND), w.s([], 'simpr', '( %s -> D e. NN )' % ND)], 'prmdvdsncoprmbd',
             '( %s -> ( E. p e. Prime %s <-> ( N gcd D ) =/= 1 ) )' % (ND, DV))
    p0e = e([], 'simpl', P0)
    bi2 = e([e([p0e], 'simp2d', 'N e. NN'), e([e([p0e], 'simp3d', 'D e. %s' % Q0S), w.inst('elfznn')], 'syl', 'D e. NN'), bi],
            'syl2anc', '( E. p e. Prime %s <-> ( N gcd D ) =/= 1 )' % DV)
    nn1 = e([bi2, ne2], 'mtbid', '-. ( N gcd D ) =/= 1')
    g0 = e([nn1, w.s([], 'nne', '( -. ( N gcd D ) =/= 1 <-> ( N gcd D ) = 1 )')], 'sylib', '( N gcd D ) = 1')
    A0 = '( ( Q e. RR /\\ N e. NN /\\ %s ) /\\ D e. %s )' % (SN, Q0S)
    a = mk(w, A0)
    e0 = a([a([a([], 'simpl1', 'Q e. RR'), a([], 'simpl2', 'N e. NN'), a([], 'simpr', 'D e. %s' % Q0S)], '3jca', P0),
            a([], 'simpl3', SN)], 'jca', E0)
    w.qed([e0, g0], 'syl', S['lscopsift'])
    return w

def lspwf():
    w = W('lspwf', 'A point of [ X , Y ] is within ( Y - X ) / 2 + 1 of the floor of the midpoint '
          '(the frequency bound of pointwise_window_bound, with the real window ends).')
    A0 = '( ( X e. RR /\\ Y e. RR ) /\\ ( N e. RR /\\ X <_ N /\\ N <_ Y ) )'
    s = mk(w, A0)
    xr = s([], 'simpll', 'X e. RR'); yr = s([], 'simplr', 'Y e. RR')
    nr = s([], 'simpr1', 'N e. RR'); xn = s([], 'simpr2', 'X <_ N'); ny = s([], 'simpr3', 'N <_ Y')
    C = '( ( X + Y ) / 2 )'
    cr = s([s([xr, yr], 'readdcld', '( X + Y ) e. RR')], 'rehalfcld', '%s e. RR' % C)
    M = '( |_ ` %s )' % C
    mr = s([s([cr], 'flcld', '%s e. ZZ' % M)], 'zred', '%s e. RR' % M)
    m1 = s([cr, w.inst('flle')], 'syl', '%s <_ %s' % (M, C))
    m2 = s([cr, w.inst('flltp1')], 'syl', '%s < ( %s + 1 )' % (C, M))
    E = '( ( ( Y - X ) / 2 ) + 1 )'
    lv = {'X': xr, 'Y': yr, 'N': nr, M: mr}
    er = s([s([s([yr, xr], 'resubcld', '( Y - X ) e. RR')], 'rehalfcld', '( ( Y - X ) / 2 ) e. RR'), a1(w, A0, '1re', '1 e. RR')], 'readdcld', '%s e. RR' % E)
    lo = linarith(w, A0, [xn, m1], '-u %s <_ ( N - %s )' % (E, M), leaves=lv, atoms=[M])
    hi = linarith(w, A0, [ny, m2], '( N - %s ) <_ %s' % (M, E), leaves=lv, atoms=[M])
    ab = s([s([nr, mr], 'resubcld', '( N - %s ) e. RR' % M), er], 'absled', '( ( abs ` ( N - %s ) ) <_ %s <-> ( -u %s <_ ( N - %s ) /\\ ( N - %s ) <_ %s ) )' % (M, E, E, M, M, E))
    w.qed([ab, s([lo, hi], 'jca', '( -u %s <_ ( N - %s ) /\\ ( N - %s ) <_ %s )' % (E, M, M, E))], 'mpbird', S['lspwf'])
    return w


def h8re(w, ante, tre, t1):
    """( ante -> H8 e. RR+ )"""
    s = mk(w, ante)
    tpos = linarith(w, ante, [t1], '0 < T', leaves={'T': tre})
    trp = s([tre, tpos], 'elrpd', 'T e. RR+')
    r8 = w.s([w.s([w.s([], '8re', '8 e. RR'), w.s([], '8pos', '0 < 8')], 'elrpii', '8 e. RR+')], 'a1i', '( %s -> 8 e. RR+ )' % ante)
    return s([a1(w, ante, 'pirp', '_pi e. RR+'), s([r8, trp], 'rpmulcld', '( 8 x. T ) e. RR+')], 'rpdivcld', '%s e. RR+' % H8)


def lspwin():
    from z4dlib import LO, HI
    w = W('lspwin', 'A member n of the log-window around -u u lies between exp ( -u u - H ) and exp ( -u u + H ) '
          '(Lean pointwise_window_bound hwin).')
    A0 = '( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ N e. NN ) /\\ ( abs ` ( -u ( log ` N ) - u ) ) <_ %s )' % H8
    s = mk(w, A0)
    tt = s([], 'simp1', '( T e. RR /\\ 1 <_ T )')
    tre = s([tt], 'simpld', 'T e. RR'); t1 = s([tt], 'simprd', '1 <_ T')
    un = s([], 'simp2', '( u e. RR /\\ N e. NN )')
    ure = s([un], 'simpld', 'u e. RR'); nnn = s([un], 'simprd', 'N e. NN')
    cnd = s([], 'simp3', '( abs ` ( -u ( log ` N ) - u ) ) <_ %s' % H8)
    hre = s([h8re(w, A0, tre, t1)], 'rpred', '%s e. RR' % H8)
    nrp = s([nnn], 'nnrpd', 'N e. RR+')
    LG = '( log ` N )'
    lg = s([nrp], 'relogcld', '%s e. RR' % LG)
    ad = s([s([lg], 'renegcld', '-u %s e. RR' % LG), ure, hre, w.inst('absdifle')], 'syl3anc',
           '( ( abs ` ( -u %s - u ) ) <_ %s <-> ( ( u - %s ) <_ -u %s /\\ -u %s <_ ( u + %s ) ) )' % (LG, H8, H8, LG, LG, H8))
    both = s([ad, cnd], 'mpbid', '( ( u - %s ) <_ -u %s /\\ -u %s <_ ( u + %s ) )' % (H8, LG, LG, H8))
    lv = {'u': ure, LG: lg, H8: hre}
    l1 = linarith(w, A0, [s([both], 'simprd', '-u %s <_ ( u + %s )' % (LG, H8))], '( -u u - %s ) <_ %s' % (H8, LG), leaves=lv, atoms=[H8, LG])
    l2 = linarith(w, A0, [s([both], 'simpld', '( u - %s ) <_ -u %s' % (H8, LG))], '%s <_ ( -u u + %s )' % (LG, H8), leaves=lv, atoms=[H8, LG])
    a = s([s([ure], 'renegcld', '-u u e. RR'), hre], 'resubcld', '( -u u - %s ) e. RR' % H8)
    b = s([s([ure], 'renegcld', '-u u e. RR'), hre], 'readdcld', '( -u u + %s ) e. RR' % H8)
    e1 = s([s([a, lg, w.inst('efle')], 'syl2anc', '( ( -u u - %s ) <_ %s <-> %s <_ ( exp ` %s ) )' % (H8, LG, LO, LG)), l1], 'mpbid',
           '%s <_ ( exp ` %s )' % (LO, LG))
    e2 = s([s([lg, b, w.inst('efle')], 'syl2anc', '( %s <_ ( -u u + %s ) <-> ( exp ` %s ) <_ %s )' % (LG, H8, LG, HI)), l2], 'mpbid',
           '( exp ` %s ) <_ %s' % (LG, HI))
    rl = s([nrp, w.inst('reeflog')], 'syl', '( exp ` %s ) = N' % LG)
    w.qed([s([e1, rl], 'breqtrd', '%s <_ N' % LO), s([rl, e2], 'eqbrtrrd', 'N <_ %s' % HI)], 'jca', S['lspwin'])
    return w


def h2d4(w, ante, tre, trp):
    """( ante -> ( 2 x. H8 ) = D4 )"""
    from mvlib import ringeq
    from cl import Closure
    s = mk(w, ante)
    cl = Closure(w, ante, {'T': tre})
    F4 = '( 4 x. T )'
    f8 = ringeq(w, ante, '( 8 x. T )', '( 2 x. %s )' % F4, cl)
    tc = s([tre], 'recnd', 'T e. CC')
    f4c = s([a1(w, ante, '4cn', '4 e. CC'), tc], 'mulcld', '%s e. CC' % F4)
    f4ne = s([s([a1(w, ante, '4rp', '4 e. RR+'), trp], 'rpmulcld', '%s e. RR+' % F4)], 'rpne0d', '%s =/= 0' % F4)
    twoc = a1(w, ante, '2cn', '2 e. CC'); twone = a1(w, ante, '2ne0', '2 =/= 0')
    pic = a1(w, ante, 'picn', '_pi e. CC')
    c5 = s([pic, f4c, twoc, f4ne, twone], 'divcan5d', '( ( 2 x. _pi ) / ( 2 x. %s ) ) = ( _pi / %s )' % (F4, F4))
    da = s([twoc, pic, s([twoc, f4c], 'mulcld', '( 2 x. %s ) e. CC' % F4), s([twoc, f4c, twone, f4ne], 'mulne0d', '( 2 x. %s ) =/= 0' % F4)],
           'divassd', '( ( 2 x. _pi ) / ( 2 x. %s ) ) = ( 2 x. ( _pi / ( 2 x. %s ) ) )' % (F4, F4))
    h8 = s([s([f8], 'oveq2d', '%s = ( _pi / ( 2 x. %s ) )' % (H8, F4))], 'oveq2d', '( 2 x. %s ) = ( 2 x. ( _pi / ( 2 x. %s ) ) )' % (H8, F4))
    return s([h8, s([da, c5], 'eqtr3d', '( 2 x. ( _pi / ( 2 x. %s ) ) ) = ( _pi / %s )' % (F4, F4))], 'eqtrd', '( 2 x. %s ) = %s' % (H8, D4))


def lspwe():
    from z4dlib import LO, HI, EE
    w = W('lspwe', 'The window width is at most rho times any of its members: 4 pi E <_ 2 pi rho N + 4 pi '
          '(Lean pointwise_window_bound hBA, hweight).')
    A0 = '( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ N e. RR ) /\\ %s <_ N )' % LO
    s = mk(w, A0)
    tt = s([], 'simp1', '( T e. RR /\\ 1 <_ T )')
    tre = s([tt], 'simpld', 'T e. RR'); t1 = s([tt], 'simprd', '1 <_ T')
    un = s([], 'simp2', '( u e. RR /\\ N e. RR )')
    ure = s([un], 'simpld', 'u e. RR'); nre = s([un], 'simprd', 'N e. RR')
    ln = s([], 'simp3', '%s <_ N' % LO)
    tpos = linarith(w, A0, [t1], '0 < T', leaves={'T': tre})
    trp = s([tre, tpos], 'elrpd', 'T e. RR+')
    h8 = h8re(w, A0, tre, t1)
    hre = s([h8], 'rpred', '%s e. RR' % H8)
    d4 = h2d4(w, A0, tre, trp)
    A = '( -u u - %s )' % H8
    ar = s([s([ure], 'renegcld', '-u u e. RR'), hre], 'resubcld', '%s e. RR' % A)
    H2 = '( 2 x. %s )' % H8
    h2r = s([a1(w, A0, '2re', '2 e. RR'), hre], 'remulcld', '%s e. RR' % H2)
    sq = lineq(w, A0, '( -u u + %s )' % H8, '( %s + %s )' % (A, H2), leaves={'u': ure, H8: hre}, atoms=[H8])
    ea = s([s([ar], 'recnd', '%s e. CC' % A), s([h2r], 'recnd', '%s e. CC' % H2), w.inst('efadd')], 'syl2anc',
           '( exp ` ( %s + %s ) ) = ( %s x. ( exp ` %s ) )' % (A, H2, LO, H2))
    ED = '( exp ` %s )' % D4
    hi = s([s([sq], 'fveq2d', '%s = ( exp ` ( %s + %s ) )' % (HI, A, H2)),
            s([ea, s([s([d4], 'fveq2d', '( exp ` %s ) = %s' % (H2, ED))], 'oveq2d', '( %s x. ( exp ` %s ) ) = ( %s x. %s )' % (LO, H2, LO, ED))],
              'eqtrd', '( exp ` ( %s + %s ) ) = ( %s x. %s )' % (A, H2, LO, ED))], 'eqtrd', '%s = ( %s x. %s )' % (HI, LO, ED))
    d4re = s([d4, h2r], 'eqeltrrd', '%s e. RR' % D4)
    d4ge = s([d4, s([a1(w, A0, '2re', '2 e. RR'), hre, linarith(w, A0, [], '0 <_ 2', leaves={}), s([h8], 'rpge0d', '0 <_ %s' % H8)],
                    'mulge0d', '0 <_ %s' % H2)], 'breqtrrd', '0 <_ %s' % D4) if False else \
        s([s([a1(w, A0, '2re', '2 e. RR'), hre, linarith(w, A0, [], '0 <_ 2', leaves={}), s([h8], 'rpge0d', '0 <_ %s' % H8)],
             'mulge0d', '0 <_ %s' % H2), d4], 'breqtrd', '0 <_ %s' % D4)
    e0 = s([s([s([], '0red', '0 e. RR'), d4re, w.inst('efle')], 'syl2anc', '( 0 <_ %s <-> ( exp ` 0 ) <_ %s )' % (D4, ED)), d4ge], 'mpbid',
           '( exp ` 0 ) <_ %s' % ED)
    e1 = s([a1(w, A0, 'ef0', '( exp ` 0 ) = 1'), e0], 'eqbrtrrd', '1 <_ %s' % ED)
    edr = s([d4re], 'reefcld', '%s e. RR' % ED)
    lor = s([ar], 'reefcld', '%s e. RR' % LO)
    rr = s([edr, a1(w, A0, '1re', '1 e. RR')], 'resubcld', '%s e. RR' % RHO)
    r0 = linarith(w, A0, [e1], '0 <_ %s' % RHO, leaves={ED: edr}, atoms=[ED])
    p1 = s([lor, nre, rr, r0, ln], 'lemul1ad', '( %s x. %s ) <_ ( N x. %s )' % (LO, RHO, RHO))
    pir = a1(w, A0, 'pire', '_pi e. RR')
    p2pi = s([a1(w, A0, '2re', '2 e. RR'), pir], 'remulcld', '( 2 x. _pi ) e. RR')
    p2g = s([a1(w, A0, '2re', '2 e. RR'), pir, linarith(w, A0, [], '0 <_ 2', leaves={}), s([a1(w, A0, 'pirp', '_pi e. RR+')], 'rpge0d', '0 <_ _pi')],
            'mulge0d', '0 <_ ( 2 x. _pi )')
    p2 = s([s([lor, rr], 'remulcld', '( %s x. %s ) e. RR' % (LO, RHO)), s([nre, rr], 'remulcld', '( N x. %s ) e. RR' % RHO), p2pi, p2g, p1],
           'lemul2ad', '( ( 2 x. _pi ) x. ( %s x. %s ) ) <_ ( ( 2 x. _pi ) x. ( N x. %s ) )' % (LO, RHO, RHO))
    his = s([hi, s([lor, edr], 'remulcld', '( %s x. %s ) e. RR' % (LO, ED))], 'eqeltrd', '%s e. RR' % HI) if False else None
    lv = {LO: lor, ED: edr, 'N': nre, '_pi': pir, HI: s([ar, a1(w, A0, '1re', '1 e. RR')], 'id', 'x') if False else None}
    lv = {LO: lor, ED: edr, 'N': nre, '_pi': pir}
    hir = s([s([s([ure], 'renegcld', '-u u e. RR'), hre], 'readdcld', '( -u u + %s ) e. RR' % H8)], 'reefcld', '%s e. RR' % HI)
    lv[HI] = hir
    w.s([], 'dummy', 'x') if False else None
    hi2 = s([hi], 'oveq2d', '( ( 2 x. _pi ) x. %s ) = ( ( 2 x. _pi ) x. ( %s x. %s ) )' % (HI, LO, ED))
    fin = nlinarith(w, A0, [hi2, p2], S['lspwe'].split(' -> ', 1)[1][:-2], leaves=lv, atoms=[LO, ED, HI])
    last = w.lines.pop()
    w.lines.append('qed' + last[len(last.split(':', 1)[0]):])
    return w


def fget(w, name):
    for l in w.lines:
        if l.split(':', 1)[0] == name:
            return l.split('|- ', 1)[1]
    raise KeyError(name)


def lift(w, st, frm, to):
    """( frm -> X ) to ( to -> X ) by adantr steps (to nests frm on the left)"""
    f = fget(w, st)
    assert f.startswith('( %s -> ' % frm), (f[:80], frm[:80])
    X = f[len('( %s -> ' % frm):-2]
    chain = []
    cur = to
    while cur != frm:
        assert cur.startswith('( ') and cur.endswith(' )'), cur[:60]
        inner = cur[2:-2]
        # split at the top-level /\ : cur = ( L /\ R ), L may be nested
        d = 0; toks = inner.split(' '); cut = None
        for i, t in enumerate(toks):
            if t == '(':
                d += 1
            elif t == ')':
                d -= 1
            elif t == '/\\' and d == 0:
                cut = i
        Lh = ' '.join(toks[:cut])
        chain.append(cur)
        cur = Lh
    for c in reversed(chain):
        st = w.s([st], 'adantr', '( %s -> %s )' % (c, X))
    return st


COND = lambda k: '( abs ` ( -u ( log ` %s ) - u ) ) <_ %s' % (k, H8)
WSET = '{ k e. S | %s }' % COND('k')


def chcl(w, ante, xdb, nz, f='f', x='x', n='n'):
    """( ante -> ( x ` ( LZ(f) ` n ) ) e. CC ) from xdb: x e. DB(f), nz: n e. ZZ"""
    e = lambda t: w.s([], 'eqid', '%s = %s' % (t, t))
    return w.s([e('( DChr ` %s )' % f), e('( Z/nZ ` %s )' % f), e(DB(f)), e(LZ(f)), xdb, nz], 'dchrzrhcl',
               '( %s -> ( %s ` ( %s ` %s ) ) e. CC )' % (ante, x, LZ(f), n))


class Win:
    """steps about the window W = { k e. S | COND(k) } in a context"""
    def __init__(self, w):
        self.w = w
        idst = w.s([], 'id', '( k = n -> k = n )')
        self.ce, new = w.wcongr(COND('k'), {'k': 'n'}, 'k = n', {'k': idst})
        assert new == COND('n'), new
        self.el = w.s([self.ce], 'elrab', '( n e. %s <-> ( n e. S /\\ %s ) )' % (WSET, COND('n')))

    def mem(self, ante, nw):
        """from nw: ( ante -> n e. W ): ( ante -> n e. S ), ( ante -> COND(n) )"""
        w = self.w
        both = w.s([nw, self.el], 'sylib', '( %s -> ( n e. S /\\ %s ) )' % (ante, COND('n')))
        return (w.s([both], 'simpld', '( %s -> n e. S )' % ante), w.s([both], 'simprd', '( %s -> %s )' % (ante, COND('n'))))

    def conv(self, ctx, wss, sfin, X, xcl):
        """( ctx -> sum_ n e. W X = sum_ n e. S if ( COND(n) , X , 0 ) ); xcl(ante, nS) -> step ( ante -> X e. CC )"""
        w = self.w
        Cw = '( %s /\\ n e. %s )' % (ctx, WSET)
        nsw = w.s([w.s([wss], 'adantr', '( %s -> %s C_ S )' % (Cw, WSET)), w.s([], 'simpr', '( %s -> n e. %s )' % (Cw, WSET))], 'sseldd',
                  '( %s -> n e. S )' % Cw)
        ra = w.s([xcl(Cw, nsw)], 'ralrimiva', '( %s -> A. n e. %s %s e. CC )' % (ctx, WSET, X))
        fo = w.s([sfin], 'olcd', '( %s -> ( S C_ ( ZZ>= ` 1 ) \\/ S e. Fin ) )' % ctx)
        ss2 = w.s([w.s([w.s([wss, ra], 'jca', '( %s -> ( %s C_ S /\\ A. n e. %s %s e. CC ) )' % (ctx, WSET, WSET, X)), fo], 'jca',
                       '( %s -> ( ( %s C_ S /\\ A. n e. %s %s e. CC ) /\\ ( S C_ ( ZZ>= ` 1 ) \\/ S e. Fin ) ) )' % (ctx, WSET, WSET, X)),
                   w.inst('sumss2')], 'syl', '( %s -> sum_ n e. %s %s = sum_ n e. S if ( n e. %s , %s , 0 ) )' % (ctx, WSET, X, WSET, X))
        Cs = '( %s /\\ n e. S )' % ctx
        b1 = w.s([w.s([], 'simpr', '( %s -> n e. S )' % Cs)], 'biantrurd', '( %s -> ( %s <-> ( n e. S /\\ %s ) ) )' % (Cs, COND('n'), COND('n')))
        b2 = w.s([self.el], 'a1i', '( %s -> ( n e. %s <-> ( n e. S /\\ %s ) ) )' % (Cs, WSET, COND('n')))
        b = w.s([b2, b1], 'bitr4d', '( %s -> ( n e. %s <-> %s ) )' % (Cs, WSET, COND('n')))
        ib = w.s([b], 'ifbid', '( %s -> if ( n e. %s , %s , 0 ) = if ( %s , %s , 0 ) )' % (Cs, WSET, X, COND('n'), X))
        sq = w.s([ib], 'sumeq2dv', '( %s -> sum_ n e. S if ( n e. %s , %s , 0 ) = sum_ n e. S if ( %s , %s , 0 ) )' % (ctx, WSET, X, COND('n'), X))
        return w.s([ss2, sq], 'eqtrd', '( %s -> sum_ n e. %s %s = sum_ n e. S if ( %s , %s , 0 ) )' % (ctx, WSET, X, COND('n'), X))


def lspwb():
    from z4dlib import LO, HI, EE, MM, LHSU, RHSU, LOGW, WAX, AN2
    w = W('lspwb', 'The pointwise window bound: at each u the conductor-weighted character sums of the window '
          'are at most the per-n weights (Lean pointwise_window_bound, from window_sieve = lswsieve).')
    A1 = '( %s /\\ u e. RR )' % HPS
    s = mk(w, A1)
    hps = s([], 'simpl', HPS)
    X1 = '( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) )'
    X2 = '( S e. Fin /\\ S C_ NN /\\ A : S --> CC )'
    x1 = s([hps], 'simp1d', X1); x2 = s([hps], 'simp2d', X2); sift = s([hps], 'simp3d', SIFT)
    qq = s([x1], 'simpld', '( Q e. RR /\\ 2 <_ Q )'); tt = s([x1], 'simprd', '( T e. RR /\\ 1 <_ T )')
    qre = s([qq], 'simpld', 'Q e. RR'); tre = s([tt], 'simpld', 'T e. RR'); t1 = s([tt], 'simprd', '1 <_ T')
    sfin = s([x2], 'simp1d', 'S e. Fin'); ssnn = s([x2], 'simp2d', 'S C_ NN'); af = s([x2], 'simp3d', 'A : S --> CC')
    ure = s([], 'simpr', 'u e. RR')
    W_ = WSET
    WN = Win(w)
    wss = a1(w, A1, 'ssrab2', '%s C_ S' % W_)
    wfin = s([sfin, wss], 'ssfid', '%s e. Fin' % W_)
    wz = s([s([wss, ssnn], 'sstrd', '%s C_ NN' % W_), a1(w, A1, 'nnssz', 'NN C_ ZZ')], 'sstrd', '%s C_ ZZ' % W_)
    AW = '( A |` %s )' % W_
    awf = s([af, wss, w.inst('fssres')], 'syl2anc', '%s : %s --> CC' % (AW, W_))
    h8 = h8re(w, A1, tre, t1)
    hre = s([h8], 'rpred', '%s e. RR' % H8)
    nu = s([ure], 'renegcld', '-u u e. RR')
    la = s([nu, hre], 'resubcld', '( -u u - %s ) e. RR' % H8)
    lb = s([nu, hre], 'readdcld', '( -u u + %s ) e. RR' % H8)
    lor = s([la], 'reefcld', '%s e. RR' % LO); hir = s([lb], 'reefcld', '%s e. RR' % HI)
    lab = linarith(w, A1, [s([h8], 'rpge0d', '0 <_ %s' % H8)], '( -u u - %s ) <_ ( -u u + %s )' % (H8, H8), leaves={'u': ure, H8: hre}, atoms=[H8])
    lohi = s([s([la, lb, w.inst('efle')], 'syl2anc', '( ( -u u - %s ) <_ ( -u u + %s ) <-> %s <_ %s )' % (H8, H8, LO, HI)), lab], 'mpbid',
             '%s <_ %s' % (LO, HI))
    mz = s([s([s([lor, hir], 'readdcld', '( %s + %s ) e. RR' % (LO, HI))], 'rehalfcld', '( ( %s + %s ) / 2 ) e. RR' % (LO, HI))], 'flcld',
           '%s e. ZZ' % MM)
    epos = linarith(w, A1, [lohi], '0 < %s' % EE, leaves={LO: lor, HI: hir}, atoms=[LO, HI])
    er = s([s([s([hir, lor], 'resubcld', '( %s - %s ) e. RR' % (HI, LO))], 'rehalfcld', '( ( %s - %s ) / 2 ) e. RR' % (HI, LO)),
            a1(w, A1, '1re', '1 e. RR')], 'readdcld', '%s e. RR' % EE)
    erp = s([er, epos], 'elrpd', '%s e. RR+' % EE)
    # COPQ
    Q0 = '( 1 ... ( |_ ` Q ) )'
    Cm = '( %s /\\ ( s e. %s /\\ m e. %s ) )' % (A1, Q0, W_)
    c = mk(w, Cm)
    msv = c([w.s([wss], 'adantr', '( %s -> %s C_ S )' % (Cm, W_)), c([], 'simprr', 'm e. %s' % W_)], 'sseldd', 'm e. S')
    mnn = c([w.s([ssnn], 'adantr', '( %s -> S C_ NN )' % Cm), msv], 'sseldd', 'm e. NN')
    idk = w.s([], 'id', '( k = m -> k = m )')
    PK = 'A. p e. Prime ( p || k -> Q < p )'
    ck, pm = w.wcongr(PK, {'k': 'm'}, 'k = m', {'k': idk})
    sm = c([ck, w.s([sift], 'adantr', '( %s -> %s )' % (Cm, SIFT)), msv], 'rspcdva', pm)
    gc = c([c([c([w.s([qre], 'adantr', '( %s -> Q e. RR )' % Cm), mnn, sm], '3jca', '( Q e. RR /\\ m e. NN /\\ %s )' % pm),
               c([], 'simprl', 's e. %s' % Q0)], 'jca', '( ( Q e. RR /\\ m e. NN /\\ %s ) /\\ s e. %s )' % (pm, Q0)), w.inst('lscopsift')],
           'syl', '( m gcd s ) = 1')
    copq = s([gc], 'ralrimivva', 'A. s e. %s A. m e. %s ( m gcd s ) = 1' % (Q0, W_))
    # FRQ
    Dm = '( %s /\\ m e. %s )' % (A1, W_)
    d = mk(w, Dm)
    ce2, cm2 = w.wcongr(COND('k'), {'k': 'm'}, 'k = m', {'k': idk})
    elm = w.s([ce2], 'elrab', '( m e. %s <-> ( m e. S /\\ %s ) )' % (W_, cm2))
    bm = d([d([], 'simpr', 'm e. %s' % W_), elm], 'sylib', '( m e. S /\\ %s )' % cm2)
    mnn2 = d([w.s([ssnn], 'adantr', '( %s -> S C_ NN )' % Dm), d([bm], 'simpld', 'm e. S')], 'sseldd', 'm e. NN')
    lm = d([d([w.s([tt], 'adantr', '( %s -> ( T e. RR /\\ 1 <_ T ) )' % Dm), d([w.s([ure], 'adantr', '( %s -> u e. RR )' % Dm), mnn2], 'jca', '( u e. RR /\\ m e. NN )'),
                d([bm], 'simprd', cm2)], '3jca', '( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ m e. NN ) /\\ %s )' % cm2), w.inst('lspwin')], 'syl',
           '( %s <_ m /\\ m <_ %s )' % (LO, HI))
    fm = d([d([w.s([lor], 'adantr', '( %s -> %s e. RR )' % (Dm, LO)), w.s([hir], 'adantr', '( %s -> %s e. RR )' % (Dm, HI))], 'jca',
              '( %s e. RR /\\ %s e. RR )' % (LO, HI)),
            d([d([mnn2], 'nnred', 'm e. RR'), d([lm], 'simpld', '%s <_ m' % LO), d([lm], 'simprd', 'm <_ %s' % HI)], '3jca',
              '( m e. RR /\\ %s <_ m /\\ m <_ %s )' % (LO, HI)), w.inst('lspwf')], 'syl2anc', '( abs ` ( m - %s ) ) <_ %s' % (MM, EE))
    frq = s([fm], 'ralrimiva', 'A. m e. %s ( abs ` ( m - %s ) ) <_ %s' % (W_, MM, EE))
    HW_ = '( %s e. Fin /\\ %s C_ ZZ /\\ %s : %s --> CC )' % (W_, W_, AW, W_)
    hw = s([wfin, wz, awf], '3jca', HW_)
    HWIN_ = '( ( Q e. RR /\\ 2 <_ Q ) /\\ ( %s /\\ %s e. ZZ ) /\\ ( %s e. RR+ /\\ A. s e. %s A. m e. %s ( m gcd s ) = 1 /\\ A. m e. %s ( abs ` ( m - %s ) ) <_ %s ) )' % (
        HW_, MM, EE, Q0, W_, W_, MM, EE)
    hwin = s([qq, s([hw, mz], 'jca', '( %s /\\ %s e. ZZ )' % (HW_, MM)), s([erp, copq, frq], '3jca',
              '( %s e. RR+ /\\ A. s e. %s A. m e. %s ( m gcd s ) = 1 /\\ A. m e. %s ( abs ` ( m - %s ) ) <_ %s )' % (EE, Q0, W_, W_, MM, EE))],
             '3jca', HWIN_)
    CHI = '( x ` ( %s ` n ) )' % LZ('f')
    WSW = 'sum_ n e. %s ( ( %s ` n ) x. %s )' % (W_, AW, CHI)
    BLKW = 'sum_ x e. %s ( ( abs ` %s ) ^ 2 )' % (PC('f'), WSW)
    LW = 'sum_ f e. %s ( %s x. %s )' % (Q0, LOGW, BLKW)
    K = '( ( Q ^ 2 ) + ( ( 4 x. _pi ) x. %s ) )' % EE
    SWW = 'sum_ n e. %s ( ( abs ` ( %s ` n ) ) ^ 2 )' % (W_, AW)
    sv = s([hwin, w.inst('lswsieve')], 'syl', '%s <_ ( %s x. %s )' % (LW, K, SWW))
    # ---- the left side: window sums with the restricted coefficients -> indicator sums over S
    AF = '( %s /\\ f e. %s )' % (A1, Q0)
    af_ = mk(w, AF)
    F2 = '( %s /\\ x e. %s )' % (AF, PC('f'))
    g = mk(w, F2)
    L = lambda st, frm, to: lift(w, st, frm, to)
    fnn = af_([af_([], 'simpr', 'f e. %s' % Q0), w.inst('elfznn')], 'syl', 'f e. NN')
    xdb = g([g([], 'simpr', 'x e. %s' % PC('f')), w.inst('elrabi')], 'syl', 'x e. %s' % DB('f'))
    F2n = '( %s /\\ n e. %s )' % (F2, W_)
    fr = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (F2n, W_)), w.inst('fvres')], 'syl', '( %s -> ( %s ` n ) = ( A ` n ) )' % (F2n, AW))
    t1_ = w.s([fr], 'oveq1d', '( %s -> ( ( %s ` n ) x. %s ) = %s )' % (F2n, AW, CHI, AX))
    WAXW = 'sum_ n e. %s %s' % (W_, AX)
    e1 = g([t1_], 'sumeq2dv', '%s = %s' % (WSW, WAXW))
    def xcl(ante, nS):
        an = w.s([L(af, A1, ante), nS], 'ffvelcdmd', '( %s -> ( A ` n ) e. CC )' % ante)
        nz = w.s([w.s([L(ssnn, A1, ante), nS], 'sseldd', '( %s -> n e. NN )' % ante)], 'nnzd', '( %s -> n e. ZZ )' % ante)
        return w.s([an, chcl(w, ante, L(xdb, F2, ante), nz)], 'mulcld', '( %s -> %s e. CC )' % (ante, AX))
    e2 = WN.conv(F2, L(wss, A1, F2), L(sfin, A1, F2), AX, xcl)
    e12 = g([e1, e2], 'eqtrd', '%s = %s' % (WSW, WAX))
    e3 = g([g([e12], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (WSW, WAX))], 'oveq1d', '( ( abs ` %s ) ^ 2 ) = %s' % (WSW, ABS2(WAX)))
    BLKU = 'sum_ x e. %s %s' % (PC('f'), ABS2(WAX))
    e4 = af_([e3], 'sumeq2dv', '%s = %s' % (BLKW, BLKU))
    e5 = af_([e4], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (LOGW, BLKW, LOGW, BLKU))
    eL = s([e5], 'sumeq2dv', '%s = %s' % (LW, LHSU))
    # realness of the left side
    qpos = linarith(w, AF, [L(s([qq], 'simprd', '2 <_ Q'), A1, AF)], '0 < Q', leaves={'Q': L(qre, A1, AF)})
    lg = af_([af_([af_([L(qre, A1, AF), qpos], 'elrpd', 'Q e. RR+'), af_([fnn], 'nnrpd', 'f e. RR+')], 'rpdivcld', '( Q / f ) e. RR+')],
             'relogcld', '%s e. RR' % LOGW)
    bk = af_([af_([fnn, L(hw, A1, AF)], 'jca', '( f e. NN /\\ %s )' % HW_), w.inst('lsblkre')], 'syl', '( %s e. RR /\\ 0 <_ %s )' % (BLKW, BLKW))
    lwr = s([a1(w, A1, 'fzfi', '%s e. Fin' % Q0), af_([lg, af_([bk], 'simpld', '%s e. RR' % BLKW)], 'remulcld', '( %s x. %s ) e. RR' % (LOGW, BLKW))],
            'fsumrecl', '%s e. RR' % LW)
    # ---- the right side
    Cn = '( %s /\\ n e. %s )' % (A1, W_)
    cn = mk(w, Cn)
    nS, cnd = WN.mem(Cn, cn([], 'simpr', 'n e. %s' % W_))
    nnn = cn([L(ssnn, A1, Cn), nS], 'sseldd', 'n e. NN')
    anc = cn([L(af, A1, Cn), nS], 'ffvelcdmd', '( A ` n ) e. CC')
    an2 = cn([cn([anc], 'abscld', '( abs ` ( A ` n ) ) e. RR')], 'resqcld', '%s e. RR' % AN2)
    an2g = cn([cn([anc], 'abscld', '( abs ` ( A ` n ) ) e. RR')], 'sqge0d', '0 <_ %s' % AN2)
    frn = cn([cn([], 'simpr', 'n e. %s' % W_), w.inst('fvres')], 'syl', '( %s ` n ) = ( A ` n )' % AW)
    q1 = cn([cn([frn], 'fveq2d', '( abs ` ( %s ` n ) ) = ( abs ` ( A ` n ) )' % AW)], 'oveq1d', '( ( abs ` ( %s ` n ) ) ^ 2 ) = %s' % (AW, AN2))
    SWA = 'sum_ n e. %s %s' % (W_, AN2)
    sww = s([q1], 'sumeq2dv', '%s = %s' % (SWW, SWA))
    pir = a1(w, A1, 'pire', '_pi e. RR')
    kr = s([s([qre], 'resqcld', '( Q ^ 2 ) e. RR'), s([s([a1(w, A1, '4re', '4 e. RR'), pir], 'remulcld', '( 4 x. _pi ) e. RR'), er], 'remulcld',
             '( ( 4 x. _pi ) x. %s ) e. RR' % EE)], 'readdcld', '%s e. RR' % K)
    fm2 = s([wfin, s([kr], 'recnd', '%s e. CC' % K), cn([an2], 'recnd', '%s e. CC' % AN2)], 'fsummulc2',
            '( %s x. %s ) = sum_ n e. %s ( %s x. %s )' % (K, SWA, W_, K, AN2))
    eR1 = s([s([sww], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (K, SWW, K, SWA)), fm2], 'eqtrd',
            '( %s x. %s ) = sum_ n e. %s ( %s x. %s )' % (K, SWW, W_, K, AN2))
    lw1 = cn([cn([L(tt, A1, Cn), cn([L(ure, A1, Cn), nnn], 'jca', '( u e. RR /\\ n e. NN )'), cnd], '3jca',
                 '( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ n e. NN ) /\\ %s )' % COND('n')), w.inst('lspwin')], 'syl',
             '( %s <_ n /\\ n <_ %s )' % (LO, HI))
    nre = cn([nnn], 'nnred', 'n e. RR')
    we = cn([cn([L(tt, A1, Cn), cn([L(ure, A1, Cn), nre], 'jca', '( u e. RR /\\ n e. RR )'), cn([lw1], 'simpld', '%s <_ n' % LO)], '3jca',
                '( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ n e. RR ) /\\ %s <_ n )' % LO), w.inst('lspwe')], 'syl',
            '( ( 4 x. _pi ) x. %s ) <_ ( ( ( ( 2 x. _pi ) x. %s ) x. n ) + ( 4 x. _pi ) )' % (EE, RHO))
    FE = '( ( 4 x. _pi ) x. %s )' % EE
    TP = '( ( ( 2 x. _pi ) x. %s ) x. n )' % RHO
    fer = L(s([s([a1(w, A1, '4re', '4 e. RR'), pir], 'remulcld', '( 4 x. _pi ) e. RR'), er], 'remulcld', '%s e. RR' % FE), A1, Cn)
    rhr = L(s([s([s([pir, s([a1(w, A1, '4re', '4 e. RR'), tre], 'remulcld', '( 4 x. T ) e. RR'),
                     s([s([a1(w, A1, '4rp', '4 e. RR+'), s([tre, linarith(w, A1, [t1], '0 < T', leaves={'T': tre})], 'elrpd', 'T e. RR+')], 'rpmulcld', '( 4 x. T ) e. RR+')],
                       'rpne0d', '( 4 x. T ) =/= 0')], 'redivcld', '%s e. RR' % D4)], 'reefcld', '( exp ` %s ) e. RR' % D4), a1(w, A1, '1re', '1 e. RR')],
              'resubcld', '%s e. RR' % RHO), A1, Cn)
    tpr = cn([cn([cn([a1(w, Cn, '2re', '2 e. RR'), L(pir, A1, Cn)], 'remulcld', '( 2 x. _pi ) e. RR'), rhr], 'remulcld', '( ( 2 x. _pi ) x. %s ) e. RR' % RHO),
              nre], 'remulcld', '%s e. RR' % TP)
    q2r = L(s([qre], 'resqcld', '( Q ^ 2 ) e. RR'), A1, Cn)
    kle = linarith(w, Cn, [we], '%s <_ %s' % (K, GW()), leaves={FE: fer, TP: tpr, '( Q ^ 2 )': q2r, '_pi': L(pir, A1, Cn)}, atoms=[FE, TP, '( Q ^ 2 )'])
    gwr = cn([cn([q2r, tpr], 'readdcld', '( ( Q ^ 2 ) + %s ) e. RR' % TP), cn([a1(w, Cn, '4re', '4 e. RR'), L(pir, A1, Cn)], 'remulcld', '( 4 x. _pi ) e. RR')],
             'readdcld', '%s e. RR' % GW())
    krn = L(kr, A1, Cn)
    ml = cn([krn, gwr, an2, an2g, kle], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (K, AN2, GW(), AN2))
    fle = s([wfin, cn([krn, an2], 'remulcld', '( %s x. %s ) e. RR' % (K, AN2)), cn([gwr, an2], 'remulcld', '( %s x. %s ) e. RR' % (GW(), AN2)), ml],
            'fsumle', 'sum_ n e. %s ( %s x. %s ) <_ sum_ n e. %s ( %s x. %s )' % (W_, K, AN2, W_, GW(), AN2))
    GA = '( %s x. %s )' % (GW(), AN2)
    def gcl(ante, nS2):
        an_ = w.s([L(af, A1, ante), nS2], 'ffvelcdmd', '( %s -> ( A ` n ) e. CC )' % ante)
        nn_ = w.s([L(ssnn, A1, ante), nS2], 'sseldd', '( %s -> n e. NN )' % ante)
        tp_ = w.s([w.s([w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ante), L(pir, A1, ante)], 'remulcld', '( %s -> ( 2 x. _pi ) e. RR )' % ante),
                        L(rhr, Cn, ante) if False else L(s([s([s([pir, s([a1(w, A1, '4re', '4 e. RR'), tre], 'remulcld', '( 4 x. T ) e. RR'),
                     s([s([a1(w, A1, '4rp', '4 e. RR+'), s([tre, linarith(w, A1, [t1], '0 < T', leaves={'T': tre})], 'elrpd', 'T e. RR+')], 'rpmulcld', '( 4 x. T ) e. RR+')],
                       'rpne0d', '( 4 x. T ) =/= 0')], 'redivcld', '%s e. RR' % D4)], 'reefcld', '( exp ` %s ) e. RR' % D4), a1(w, A1, '1re', '1 e. RR')],
              'resubcld', '%s e. RR' % RHO), A1, ante)], 'remulcld', '( %s -> ( ( 2 x. _pi ) x. %s ) e. RR )' % (ante, RHO)),
                       w.s([nn_], 'nnred', '( %s -> n e. RR )' % ante)], 'remulcld', '( %s -> %s e. RR )' % (ante, TP))
        gw_ = w.s([w.s([w.s([L(qre, A1, ante)], 'resqcld', '( %s -> ( Q ^ 2 ) e. RR )' % ante), tp_], 'readdcld', '( %s -> ( ( Q ^ 2 ) + %s ) e. RR )' % (ante, TP)),
                   w.s([w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % ante), L(pir, A1, ante)], 'remulcld', '( %s -> ( 4 x. _pi ) e. RR )' % ante)],
                  'readdcld', '( %s -> %s e. RR )' % (ante, GW()))
        a2_ = w.s([w.s([an_], 'abscld', '( %s -> ( abs ` ( A ` n ) ) e. RR )' % ante)], 'resqcld', '( %s -> %s e. RR )' % (ante, AN2))
        return w.s([w.s([gw_, a2_], 'remulcld', '( %s -> %s e. RR )' % (ante, GA))], 'recnd', '( %s -> %s e. CC )' % (ante, GA))
    eR2 = WN.conv(A1, wss, sfin, GA, gcl)
    sk = s([wfin, cn([krn, an2], 'remulcld', '( %s x. %s ) e. RR' % (K, AN2))], 'fsumrecl', 'sum_ n e. %s ( %s x. %s ) e. RR' % (W_, K, AN2))
    sg = s([wfin, cn([gwr, an2], 'remulcld', '%s e. RR' % GA)], 'fsumrecl', 'sum_ n e. %s %s e. RR' % (W_, GA))
    c1 = s([sv, eR1], 'breqtrd', '%s <_ sum_ n e. %s ( %s x. %s )' % (LW, W_, K, AN2))
    c2 = s([lwr, sk, sg, c1, fle], 'letrd', '%s <_ sum_ n e. %s %s' % (LW, W_, GA))
    c3 = s([c2, eR2], 'breqtrd', '%s <_ %s' % (LW, RHSU))
    w.qed([eL, c3], 'eqbrtrrd', S['lspwb'])
    return w, None


ALL = {'lspwb': lambda: lspwb()[0], 'lspwe': lspwe, 'lspwin': lspwin, 'lspwf': lspwf, 'lscopsift': lscopsift}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
