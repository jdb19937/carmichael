"""Sortie LD1, section 4 part 1: dyadic blocks
(ld1ncov ld1exblk ld1blku ld1sblk ld1cjk0 ld1cjk0n ld1cjk0b ld1tayeq ld1rpowtay).
Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_d.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only
L = '( log ` D )'
L2 = '( log ` 2 )'
D2 = '( 2 x. D )'
RJ = '( 0 ..^ %s )' % JPAR


def fin(w):
    qedlast(w)
    return go(w)


def setupx(w, A):
    """parts, base closure, and the character/S facts when A has them"""
    P = parts(w, A)
    c, F = basecl(w, A, P)
    for k, f in [('cf', 'C : NN --> CC'), ('cb', CB), ('sc', 'S e. CC'), ('nN', 'N e. NN')]:
        if f in P:
            F[k] = P[f]
    if 'sc' in F:
        F['re'] = dst(w, A, [F['sc']], 'recld', '( Re ` S ) e. RR')
        c.leaf('S', 'CC', F['sc']); c.leaf('( Re ` S )', 'RR', F['re']); c.leaf('( Im ` S )', 'RR', dst(w, A, [F['sc']], 'imcld', '( Im ` S ) e. RR'))
    return P, c, F


def hab(w, A, F):
    dr, z = F['dr'], F['z']
    d2r = dst(w, A, [a1(w, A, '2re', '2 e. RR'), dr], 'remulcld', '%s e. RR' % D2)
    c0 = Closure(w, A, {'D': ('RR', dr)})
    lt = linarith(w, A, [z], 'D < %s' % D2, closure=c0)
    h0 = J(w, A, J(w, A, dr, z), J(w, A, d2r, lt))
    rp3 = J(w, A, F['rp'], dst(w, A, [d2r, linarith(w, A, [z], '0 < %s' % D2, closure=c0)], 'elrpd', '%s e. RR+' % D2), lt)
    return h0, rp3


def basefacts(F):
    out = [('D', 'RR+', F['rp']), ('D', 'gt1', F['d1']), (L, 'RR', F['lr']), (YP, 'RR+', F['yrp']), (YP, 'gt1', F['y1']),
           (JPAR, 'NN', F['jn']), (NMAX, 'NN', F['nn'])]
    if 'sc' in F:
        out += [('S', 'CC', F['sc']), ('( Re ` S )', 'RR', F['re'])]
    return out


def liftcl(w, A, An, facts):
    lv = {}
    for e, kind, stp in facts:
        lv.setdefault(e, []).append((kind, lift(w, stp, An)))
    return Closure(w, An, lv)


def termcl(w, An, c, n, nstep, F, rp3):
    c.leaf(n, 'NN', nstep)
    c.leaf(BVA(n), 'RR', ap(w, An, 'bvare', [lift(w, rp3, An), nstep], '%s e. RR' % BVA(n)))
    c.leaf('( C ` %s )' % n, 'CC', dst(w, An, [lift(w, F['cf'], An), nstep], 'ffvelcdmd', '( C ` %s ) e. CC' % n))
    return c


def ld1ncov():
    w = W('ld1ncov', 'Lean ` Nmax_le_two_pow_Jpar_mul ` : the blocks ` j < J ` cover ` ( D , Nmax ] ` : ` Nmax <_ 2 ^ J D ` (~ ld1nmax , ~ ld1nblk , ~ z5dlog2 , ~ cxpefd ).')
    A = HZH; P = parts(w, A); c, F = basecl(w, A, P)
    Y = YP
    nm = ap(w, A, 'ld1nmax', [F['hz']], concl('ld1nmax'))
    nle = dst(w, A, [nm], 'simp3d', '%s <_ ( ( ( 8 x. %s ) x. %s ) + 1 )' % (NMAX, Y, L))
    c.leaf(NMAX, 'RR', dst(w, A, [F['nn']], 'nnred', '%s e. RR' % NMAX))
    h1 = nlinarith(w, A, [nle, F['y4'], F['dl']], '%s <_ ( 9 x. ( %s x. %s ) )' % (NMAX, Y, L), closure=c)
    # D ^c log 2 <_ 2 ^ JPAR
    dc = c.mem('D', 'CC'); d0 = c.ne0('D')
    l2r = a1(w, A, 'relogcl' if False else 'x', 'x') if False else None
    two = dst(w, A, [a1(w, A, '2rp', '2 e. RR+')], 'relogcld', '%s e. RR' % L2)
    c.leaf(L2, 'RR', two)
    l2ge = w.s([w.s([], 'z5dlog2', '( ; 5 6 / ; 8 1 ) <_ %s' % L2)], 'a1i', '( %s -> ( ; 5 6 / ; 8 1 ) <_ %s )' % (A, L2))
    l20 = linarith(w, A, [l2ge], '0 <_ %s' % L2, closure=c); c.leaf(L2, 'ge0', l20)
    x1 = dst(w, A, [dc, d0, c.mem(L2, 'CC')], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (L2, L2, L))
    jz = dst(w, A, [F['jn']], 'nnzd', '%s e. ZZ' % JPAR)
    x2 = ap(w, A, 'cxpexp', [a1(w, A, '2cn', '2 e. CC'), dst(w, A, [F['jn']], 'nnnn0d', '%s e. NN0' % JPAR)], '( 2 ^c %s ) = ( 2 ^ %s )' % (JPAR, JPAR))
    x3 = dst(w, A, [a1(w, A, '2cn', '2 e. CC'), a1(w, A, '2ne0', '2 =/= 0'), c.mem(JPAR, 'CC')], 'cxpefd', '( 2 ^c %s ) = ( exp ` ( %s x. %s ) )' % (JPAR, JPAR, L2))
    jp = ap(w, A, 'ld1jpar', [F['hz']], concl('ld1jpar'))
    lj = dst(w, A, [dst(w, A, [jp], 'simprd', '( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) )' % (L, JPAR, JPAR, L, JPAR, L))], 'simp1d', '%s <_ %s' % (L, JPAR))
    m1 = lemul(w, A, c, lj, L2, side=1)                                                     # L log2 <_ JPAR log2
    ef1 = ap(w, A, 'efle', [c.mem('( %s x. %s )' % (L, L2), 'RR'), c.mem('( %s x. %s )' % (JPAR, L2), 'RR')], '( ( %s x. %s ) <_ ( %s x. %s ) <-> ( exp ` ( %s x. %s ) ) <_ ( exp ` ( %s x. %s ) ) )' % (L, L2, JPAR, L2, L, L2, JPAR, L2))
    e1 = dst(w, A, [m1, ef1], 'mpbid', '( exp ` ( %s x. %s ) ) <_ ( exp ` ( %s x. %s ) )' % (L, L2, JPAR, L2))
    cm = dst(w, A, [c.mem(L2, 'CC'), c.mem(L, 'CC')], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (L2, L, L, L2))
    x1b = eqt(w, A, x1, dst(w, A, [cm], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. %s ) )' % (L2, L, L, L2)))
    h2 = dst(w, A, [x1b, dst(w, A, [e1, eqt(w, A, eqc(w, A, x3), x2)], 'breqtrd', '( exp ` ( %s x. %s ) ) <_ ( 2 ^ %s )' % (L, L2, JPAR))], 'eqbrtrd', '( D ^c %s ) <_ ( 2 ^ %s )' % (L2, JPAR))
    # 9 L <_ D ^c ( log 2 - 51/100 )
    EX = '( %s - ( ; 5 1 / ; ; 1 0 0 ) )' % L2
    x4 = dst(w, A, [dc, d0, c.mem(EX, 'CC')], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (EX, EX, L))
    nb = ap(w, A, 'ld1nblk', [J(w, A, F['lr'], F['dl'])], '( 9 x. %s ) <_ ( exp ` ( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. %s ) )' % (L, L))
    l0 = linarith(w, A, [F['dl']], '0 <_ %s' % L, closure=c); c.leaf(L, 'ge0', l0)
    cc = linarith(w, A, [l2ge], '( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) <_ %s' % EX, closure=c)
    m2 = lemul(w, A, c, cc, L, side=1)                                                      # 0.1831 L <_ EX L
    ef2 = ap(w, A, 'efle', [c.mem('( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. %s )' % L, 'RR'), c.mem('( %s x. %s )' % (EX, L), 'RR')],
             '( ( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. %s ) <_ ( %s x. %s ) <-> ( exp ` ( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. %s ) ) <_ ( exp ` ( %s x. %s ) ) )' % (L, EX, L, L, EX, L))
    e2 = dst(w, A, [m2, ef2], 'mpbid', '( exp ` ( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. %s ) ) <_ ( exp ` ( %s x. %s ) )' % (L, EX, L))
    E9 = '( exp ` ( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. %s ) )' % L; EE = '( exp ` ( %s x. %s ) )' % (EX, L)
    h3 = dst(w, A, [dst(w, A, [c.mem('( 9 x. %s )' % L, 'RR'), c.mem(E9, 'RR'), c.mem(EE, 'RR'), nb, e2], 'letrd', '( 9 x. %s ) <_ %s' % (L, EE)), eqc(w, A, x4)], 'breqtrd', '( 9 x. %s ) <_ ( D ^c %s )' % (L, EX))
    # D ^c log2 x. D = YP x. D ^c EX
    p1 = dst(w, A, [dc, d0, c.mem(L2, 'CC')], 'cxpp1d', '( D ^c ( %s + 1 ) ) = ( ( D ^c %s ) x. D )' % (L2, L2))
    C151 = '( ; ; 1 5 1 / ; ; 1 0 0 )'
    p2 = dst(w, A, [dc, d0, c.mem(C151, 'CC'), c.mem(EX, 'CC')], 'cxpaddd', '( D ^c ( %s + %s ) ) = ( %s x. ( D ^c %s ) )' % (C151, EX, Y, EX))
    ee = ringeq(w, A, '( %s + %s )' % (C151, EX), '( %s + 1 )' % L2, c)
    h4 = eqt(w, A, eqc(w, A, p2), eqt(w, A, dst(w, A, [ee], 'oveq2d', '( D ^c ( %s + %s ) ) = ( D ^c ( %s + 1 ) )' % (C151, EX, L2)), p1))   # YP D^EX = D^log2 D
    # assemble
    DX = '( D ^c %s )' % EX; DL = '( D ^c %s )' % L2
    for e in (DX, DL, '( 2 ^ %s )' % JPAR):
        c.leaf(e, 'RR', c.mem(e, 'RR')); c.leaf(e, 'ge0', c.ge0(e))
    s1 = lemul(w, A, c, h3, Y)                                                              # Y ( 9 L ) <_ Y DX
    s2 = lemul(w, A, c, h2, 'D', side=1)                                                    # DL D <_ 2^J D
    r9 = ringeq(w, A, '( 9 x. ( %s x. %s ) )' % (Y, L), '( %s x. ( 9 x. %s ) )' % (Y, L), c)
    st1 = dst(w, A, [h1, r9], 'breqtrd', '%s <_ ( %s x. ( 9 x. %s ) )' % (NMAX, Y, L))
    st2 = dst(w, A, [c.mem(NMAX, 'RR'), c.mem('( %s x. ( 9 x. %s ) )' % (Y, L), 'RR'), c.mem('( %s x. %s )' % (Y, DX), 'RR'), st1, s1], 'letrd', '%s <_ ( %s x. %s )' % (NMAX, Y, DX))
    st3 = dst(w, A, [st2, h4], 'breqtrd', '%s <_ ( %s x. D )' % (NMAX, DL))
    dst(w, A, [c.mem(NMAX, 'RR'), c.mem('( %s x. D )' % DL, 'RR'), c.mem('( ( 2 ^ %s ) x. D )' % JPAR, 'RR'), st3, s2], 'letrd', '%s <_ ( ( 2 ^ %s ) x. D )' % (NMAX, JPAR))
    return fin(w)


def ld1exblk():
    w = W('ld1exblk', 'Lean ` exists_block ` : every ` n ` with ` D < n <_ 2 ^ J D ` lies in a dyadic block ` 2 ^ m D < n <_ 2 ^ ( m + 1 ) D ` with ` m < J ` (induction on ` J ` , ~ nn0indd ).')
    A = ante('ld1exblk'); P = parts(w, A)
    A0 = '( ( D e. RR /\\ 0 < D ) /\\ ( N e. NN /\\ D < N ) )'
    dr, z, nn, dn = P['D e. RR'], P['0 < D'], P['N e. NN'], P['D < N']
    jn, nle = P['J e. NN0'], P['N <_ ( ( 2 ^ J ) x. D )']
    PS = lambda x: '( N <_ ( ( 2 ^ %s ) x. D ) -> E. m e. ( 0 ..^ %s ) %s )' % (x, x, BLKC('m', 'N'))
    idx = lambda t: w.s([], 'id', '( x = %s -> x = %s )' % (t, t))
    c1, _ = w.wcongr(PS('x'), {'x': '0'}, 'x = 0', {'x': idx('0')})
    c2, _ = w.wcongr(PS('x'), {'x': 'y'}, 'x = y', {'x': idx('y')})
    c3, _ = w.wcongr(PS('x'), {'x': '( y + 1 )'}, 'x = ( y + 1 )', {'x': idx('( y + 1 )')})
    c4, _ = w.wcongr(PS('x'), {'x': 'J'}, 'x = J', {'x': idx('J')})
    # base
    P0 = parts(w, A0)
    cb = Closure(w, A0, {'D': [('RR', P0['D e. RR']), ('gt0', P0['0 < D'])], 'N': ('NN', P0['N e. NN'])})
    e0 = eqt(w, A0, dst(w, A0, [ap(w, A0, 'exp0', [cb.mem('2', 'CC')], '( 2 ^ 0 ) = 1')], 'oveq1d', '( ( 2 ^ 0 ) x. D ) = ( 1 x. D )'), dst(w, A0, [cb.mem('D', 'CC')], 'mullidd', '( 1 x. D ) = D'))
    nl = dst(w, A0, [P0['D < N'], dst(w, A0, [P0['D e. RR'], cb.mem('N', 'RR')], 'ltnled', '( D < N <-> -. N <_ D )')], 'mpbid', '-. N <_ D')
    nl2 = dst(w, A0, [nl, dst(w, A0, [e0], 'breq2d', '( N <_ ( ( 2 ^ 0 ) x. D ) <-> N <_ D )')], 'mtbird', '-. N <_ ( ( 2 ^ 0 ) x. D )')
    base = dst(w, A0, [nl2], 'pm2.21d', PS('0'))
    # step
    B = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (A0, PS('y'))
    PB = parts(w, B)
    yn = PB['y e. NN0']; ih = PB[PS('y')]
    B2 = '( %s /\\ N <_ ( ( 2 ^ ( y + 1 ) ) x. D ) )' % B
    cB = Closure(w, B2, {'D': [('RR', lift(w, PB['D e. RR'], B2)), ('gt0', lift(w, PB['0 < D'], B2))], 'N': ('NN', lift(w, PB['N e. NN'], B2)), 'y': ('NN0', lift(w, yn, B2))})
    h2 = w.s([], 'simpr', '( %s -> N <_ ( ( 2 ^ ( y + 1 ) ) x. D ) )' % B2)
    Bc = '( %s /\\ N <_ ( ( 2 ^ y ) x. D ) )' % B2
    ex1 = dst(w, Bc, [w.s([], 'simpr', '( %s -> N <_ ( ( 2 ^ y ) x. D ) )' % Bc), lift(w, ih, Bc)], 'mpd', 'E. m e. ( 0 ..^ y ) %s' % BLKC('m', 'N'))
    uz = ap(w, Bc, 'peano2uz', [ap(w, Bc, 'uzid', [dst(w, Bc, [lift(w, yn, Bc)], 'nn0zd', 'y e. ZZ')], 'y e. ( ZZ>= ` y )')], '( y + 1 ) e. ( ZZ>= ` y )')
    ss = ap(w, Bc, 'fzoss2', [uz], '( 0 ..^ y ) C_ ( 0 ..^ ( y + 1 ) )')
    case1 = dst(w, Bc, [ex1, ap(w, Bc, 'ssrexv', [ss], '( E. m e. ( 0 ..^ y ) %s -> E. m e. ( 0 ..^ ( y + 1 ) ) %s )' % (BLKC('m', 'N'), BLKC('m', 'N')))], 'mpd', 'E. m e. ( 0 ..^ ( y + 1 ) ) %s' % BLKC('m', 'N'))
    Bn = '( %s /\\ -. N <_ ( ( 2 ^ y ) x. D ) )' % B2
    cN = Closure(w, Bn, {'D': [('RR', lift(w, PB['D e. RR'], Bn)), ('gt0', lift(w, PB['0 < D'], Bn))], 'N': ('NN', lift(w, PB['N e. NN'], Bn)), 'y': ('NN0', lift(w, yn, Bn))})
    lt = dst(w, Bn, [w.s([], 'simpr', '( %s -> -. N <_ ( ( 2 ^ y ) x. D ) )' % Bn), dst(w, Bn, [cN.mem('( ( 2 ^ y ) x. D )', 'RR'), cN.mem('N', 'RR')], 'ltnled', '( ( ( 2 ^ y ) x. D ) < N <-> -. N <_ ( ( 2 ^ y ) x. D ) )')], 'mpbird', '( ( 2 ^ y ) x. D ) < N')
    bl = J(w, Bn, lt, lift(w, h2, Bn))
    assert body(w, bl, Bn) == BLKC('y', 'N')
    yin = ap(w, Bn, 'fzonn0p1', [lift(w, yn, Bn)], 'y e. ( 0 ..^ ( y + 1 ) )')
    cg, _ = w.wcongr(BLKC('m', 'N'), {'m': 'y'}, 'm = y', {'m': w.s([], 'id', '( m = y -> m = y )')})
    case2 = dst(w, Bn, [J(w, Bn, yin, bl), w.s([cg], 'rspcev', '( ( y e. ( 0 ..^ ( y + 1 ) ) /\\ %s ) -> E. m e. ( 0 ..^ ( y + 1 ) ) %s )' % (BLKC('y', 'N'), BLKC('m', 'N')))], 'syl',
                'E. m e. ( 0 ..^ ( y + 1 ) ) %s' % BLKC('m', 'N'))
    both = dst(w, B2, [case1, case2], 'pm2.61dan', 'E. m e. ( 0 ..^ ( y + 1 ) ) %s' % BLKC('m', 'N'))
    step = dst(w, B, [both], 'ex', PS('( y + 1 )'))
    ind = w.s([c1, c2, c3, c4, base, step], 'nn0indd', '( ( %s /\\ J e. NN0 ) -> %s )' % (A0, PS('J')))
    a0 = J(w, A, J(w, A, dr, z), J(w, A, nn, dn))
    et = dst(w, A, [J(w, A, a0, jn), ind], 'syl', PS('J'))
    dst(w, A, [nle, et], 'mpd', 'E. m e. ( 0 ..^ J ) %s' % BLKC('m', 'N'))
    return fin(w)


def ld1blku():
    w = W('ld1blku', 'Lean ` block_unique ` : the dyadic blocks are disjoint (~ nn0ltp1le , ~ leexp2a , ~ lttri3 ).')
    A = ante('ld1blku'); P = parts(w, A)
    dr, z, nr, jn, kn = P['D e. RR'], P['0 < D'], P['N e. RR'], P['J e. NN0'], P['K e. NN0']
    bj, bk = P[BLKC('J', 'N')], P[BLKC('K', 'N')]
    c = Closure(w, A, {'D': [('RR', dr), ('gt0', z)], 'N': ('RR', nr), 'J': ('NN0', jn), 'K': ('NN0', kn)})
    def half(X, Y, bx, by, name):
        """( A -> -. X < Y ) from BLKC(X): N <_ 2^(X+1) D and BLKC(Y): 2^Y D < N"""
        A1 = '( %s /\\ %s < %s )' % (A, X, Y)
        c1 = Closure(w, A1, {'D': [('RR', lift(w, dr, A1)), ('gt0', lift(w, z, A1))], 'N': ('RR', lift(w, nr, A1)), X: ('NN0', lift(w, P['%s e. NN0' % X], A1)), Y: ('NN0', lift(w, P['%s e. NN0' % Y], A1))})
        le = dst(w, A1, [w.s([], 'simpr', '( %s -> %s < %s )' % (A1, X, Y)), ap(w, A1, 'nn0ltp1le', [c1.mem(X, 'NN0'), c1.mem(Y, 'NN0')], '( %s < %s <-> ( %s + 1 ) <_ %s )' % (X, Y, X, Y))], 'mpbid', '( %s + 1 ) <_ %s' % (X, Y))
        uz = dst(w, A1, [J(w, A1, c1.mem('( %s + 1 )' % X, 'ZZ'), c1.mem(Y, 'ZZ'), le), a1(w, A1, 'eluz2', '( %s e. ( ZZ>= ` ( %s + 1 ) ) <-> ( ( %s + 1 ) e. ZZ /\\ %s e. ZZ /\\ ( %s + 1 ) <_ %s ) )' % (Y, X, X, Y, X, Y))], 'mpbird', '%s e. ( ZZ>= ` ( %s + 1 ) )' % (Y, X))
        lx = ap(w, A1, 'leexp2a', [c1.mem('2', 'RR'), w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % A1), uz], '( 2 ^ ( %s + 1 ) ) <_ ( 2 ^ %s )' % (X, Y))
        ld = lemul(w, A1, c1, lx, 'D', side=1)
        h2 = dst(w, A1, [lift(w, bx, A1)], 'simprd', 'N <_ ( ( 2 ^ ( %s + 1 ) ) x. D )' % X)
        h3 = dst(w, A1, [lift(w, by, A1)], 'simpld', '( ( 2 ^ %s ) x. D ) < N' % Y)
        for e in ('( ( 2 ^ ( %s + 1 ) ) x. D )' % X, '( ( 2 ^ %s ) x. D )' % Y):
            c1.leaf(e, 'RR', c1.mem(e, 'RR'))
        nn_ = linarith(w, A1, [ld, h2, h3], 'N < N', closure=c1)
        nlt = ap(w, A1, 'ltnr', [c1.mem('N', 'RR')], '-. N < N')
        return dst(w, A, [nn_, nlt], 'pm2.65da', '-. %s < %s' % (X, Y))
    n1 = half('J', 'K', bj, bk, 'jk'); n2 = half('K', 'J', bk, bj, 'kj')
    tri = ap(w, A, 'lttri3', [c.mem('J', 'RR'), c.mem('K', 'RR')], '( J = K <-> ( -. J < K /\\ -. K < J ) )')
    dst(w, A, [J(w, A, n1, n2), tri], 'mpbird', 'J = K')
    return fin(w)


def ld1sblk():
    w = W('ld1sblk', 'Lean ` sum_truncTerm_eq_sum_blockSum ` (Lemma 2.5): the truncation is the sum of its dyadic block sums (~ fsumcom , ~ ld1exblk , ~ ld1blku , ~ sumite , ~ sumz ).')
    A = ante('ld1sblk'); P, c, F = setupx(w, A)
    h0, rp3 = hab(w, A, F)
    R = FZN
    IFB = lambda m, n: 'if ( %s , %s , 0 )' % (BLKC(m, n), BODY(n))
    Amn = '( %s /\\ ( m e. %s /\\ n e. %s ) )' % (A, RJ, R)
    mn_ = w.s([], 'simprl', '( %s -> m e. %s )' % (Amn, RJ)); nn_ = w.s([], 'simprr', '( %s -> n e. %s )' % (Amn, R))
    cmn = liftcl(w, A, Amn, basefacts(F)); termcl(w, Amn, cmn, 'n', ap(w, Amn, 'elfznn', [nn_], 'n e. NN'), F, rp3)
    cmn.leaf('m', 'NN0', ap(w, Amn, 'elfzonn0', [mn_], 'm e. NN0'))
    com = w.s([a1(w, A, 'fzofi', '%s e. Fin' % RJ), dst(w, A, [], 'fzfid', '%s e. Fin' % R), cmn.mem(IFB('m', 'n'), 'CC')], 'fsumcom',
              '( %s -> sum_ m e. %s sum_ n e. %s %s = sum_ n e. %s sum_ m e. %s %s )' % (A, RJ, R, IFB('m', 'n'), R, RJ, IFB('m', 'n')))
    # per n
    An = '( %s /\\ n e. %s )' % (A, R)
    nR = w.s([], 'simpr', '( %s -> n e. %s )' % (An, R))
    nN = ap(w, An, 'elfznn', [nR], 'n e. NN')
    cn = liftcl(w, A, An, basefacts(F)); termcl(w, An, cn, 'n', nN, F, rp3)
    SM = 'sum_ m e. %s %s' % (RJ, IFB('m', 'n'))
    An1 = '( %s /\\ D < n )' % An
    c1 = liftcl(w, A, An1, basefacts(F)); termcl(w, An1, c1, 'n', lift(w, nN, An1), F, rp3)
    nle = ap(w, An1, 'elfzle2', [lift(w, nR, An1)], 'n <_ %s' % NMAX)
    cov = ap(w, An1, 'ld1ncov', [lift(w, F['hz'], An1)], concl('ld1ncov'))
    n2j = dst(w, An1, [c1.mem('n', 'RR'), c1.mem(NMAX, 'RR'), c1.mem('( ( 2 ^ %s ) x. D )' % JPAR, 'RR'), nle, cov], 'letrd', 'n <_ ( ( 2 ^ %s ) x. D )' % JPAR)
    exb = ap(w, An1, 'ld1exblk', [J(w, An1, J(w, An1, lift(w, F['dr'], An1), lift(w, F['z'], An1)), J(w, An1, lift(w, nN, An1), w.s([], 'simpr', '( %s -> D < n )' % An1)), J(w, An1, c1.mem(JPAR, 'NN0'), n2j))],
             'E. m e. %s %s' % (RJ, BLKC('m', 'n')))
    cg0, _ = w.wcongr(BLKC('m', 'n'), {'m': 'q'}, 'm = q', {'m': w.s([], 'id', '( m = q -> m = q )')})
    exb = dst(w, An1, [exb, w.s([cg0], 'cbvrexvw', '( E. m e. %s %s <-> E. q e. %s %s )' % (RJ, BLKC('m', 'n'), RJ, BLKC('q', 'n')))], 'sylib', 'E. q e. %s %s' % (RJ, BLKC('q', 'n')))
    Aq = '( %s /\\ ( q e. %s /\\ %s ) )' % (An1, RJ, BLKC('q', 'n'))
    qin = w.s([], 'simprl', '( %s -> q e. %s )' % (Aq, RJ)); bq = w.s([], 'simprr', '( %s -> %s )' % (Aq, BLKC('q', 'n')))
    cq = liftcl(w, A, Aq, basefacts(F)); termcl(w, Aq, cq, 'n', lift(w, nN, Aq), F, rp3)
    Aqm = '( %s /\\ m e. %s )' % (Aq, RJ)
    mR = w.s([], 'simpr', '( %s -> m e. %s )' % (Aqm, RJ))
    cqm = liftcl(w, A, Aqm, basefacts(F)); termcl(w, Aqm, cqm, 'n', lift(w, nN, Aqm), F, rp3)
    # BLKC(m,n) <-> m = q
    Ab = '( %s /\\ %s )' % (Aqm, BLKC('m', 'n'))
    fwd = ap(w, Ab, 'ld1blku', [J(w, Ab, J(w, Ab, lift(w, F['dr'], Ab), lift(w, F['z'], Ab)), lift(w, cqm.mem('n', 'RR'), Ab)),
                                 J(w, Ab, J(w, Ab, ap(w, Ab, 'elfzonn0', [lift(w, mR, Ab)], 'm e. NN0'), ap(w, Ab, 'elfzonn0', [lift(w, qin, Ab)], 'q e. NN0')),
                                   J(w, Ab, w.s([], 'simpr', '( %s -> %s )' % (Ab, BLKC('m', 'n'))), lift(w, bq, Ab)))], 'm = q')
    Ae = '( %s /\\ m = q )' % Aqm
    cg, _ = w.wcongr(BLKC('m', 'n'), {'m': 'q'}, 'm = q', {'m': w.s([], 'id', '( m = q -> m = q )')})
    bwd = dst(w, Ae, [lift(w, bq, Ae), dst(w, Ae, [w.s([], 'simpr', '( %s -> m = q )' % Ae), cg], 'syl', '( %s <-> %s )' % (BLKC('m', 'n'), BLKC('q', 'n')))], 'mpbird', BLKC('m', 'n'))
    bi = dst(w, Aqm, [fwd, bwd], 'impbida', '( %s <-> m = q )' % BLKC('m', 'n'))
    ife = dst(w, Aqm, [bi], 'ifbid', '%s = if ( m = q , %s , 0 )' % (IFB('m', 'n'), BODY('n')))
    se = dst(w, Aq, [ife], 'sumeq2dv', '%s = sum_ m e. %s if ( m = q , %s , 0 )' % (SM, RJ, BODY('n')))
    si = w.s([w.s([], 'eqidd', '( m = q -> %s = %s )' % (BODY('n'), BODY('n'))), a1(w, Aq, 'fzofi', '%s e. Fin' % RJ), qin, cq.mem(BODY('n'), 'CC')], 'sumite',
             '( %s -> sum_ m e. %s if ( m = q , %s , 0 ) = %s )' % (Aq, RJ, BODY('n'), BODY('n')))
    vq = eqt(w, Aq, se, si)
    v1 = w.s([exb, vq], 'rexlimddv', '( %s -> %s = %s )' % (An1, SM, BODY('n')))
    t1 = dst(w, An1, [w.s([], 'simpr', '( %s -> D < n )' % An1)], 'iftrued', '%s = %s' % (TT('n'), BODY('n')))
    case1 = dst(w, An1, [v1, t1], 'eqtr4d', '%s = %s' % (SM, TT('n')))
    # -. D < n
    An2 = '( %s /\\ -. D < n )' % An
    c2 = liftcl(w, A, An2, basefacts(F)); termcl(w, An2, c2, 'n', lift(w, nN, An2), F, rp3)
    Am2 = '( %s /\\ m e. %s )' % (An2, RJ)
    cm2 = liftcl(w, A, Am2, basefacts(F)); termcl(w, Am2, cm2, 'n', lift(w, nN, Am2), F, rp3)
    cm2.leaf('m', 'NN0', ap(w, Am2, 'elfzonn0', [w.s([], 'simpr', '( %s -> m e. %s )' % (Am2, RJ))], 'm e. NN0'))
    nd = dst(w, Am2, [lift(w, w.s([], 'simpr', '( %s -> -. D < n )' % An2), Am2), dst(w, Am2, [cm2.mem('n', 'RR'), cm2.mem('D', 'RR')], 'lenltd', '( n <_ D <-> -. D < n )')], 'mpbird', 'n <_ D')
    g1 = ap(w, Am2, 'expge1', [J(w, Am2, cm2.mem('2', 'RR'), cm2.mem('m', 'NN0'), w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % Am2))], '1 <_ ( 2 ^ m )')
    dd = dst(w, Am2, [lemul(w, Am2, cm2, g1, 'D', side=1)], 'x', 'x') if False else lemul(w, Am2, cm2, g1, 'D', side=1)     # 1 D <_ 2^m D
    dd2 = dst(w, Am2, [dst(w, Am2, [cm2.mem('D', 'CC')], 'mullidd', '( 1 x. D ) = D'), dd], 'eqbrtrrd', 'D <_ ( ( 2 ^ m ) x. D )')
    cm2.leaf('( ( 2 ^ m ) x. D )', 'RR', cm2.mem('( ( 2 ^ m ) x. D )', 'RR'))
    nle2 = linarith(w, Am2, [nd, dd2], 'n <_ ( ( 2 ^ m ) x. D )', closure=cm2)
    nlt = dst(w, Am2, [nle2, dst(w, Am2, [cm2.mem('n', 'RR'), cm2.mem('( ( 2 ^ m ) x. D )', 'RR')], 'lenltd', '( n <_ ( ( 2 ^ m ) x. D ) <-> -. ( ( 2 ^ m ) x. D ) < n )')], 'mpbid', '-. ( ( 2 ^ m ) x. D ) < n')
    nb = dst(w, Am2, [nlt], 'intnanrd', '-. %s' % BLKC('m', 'n'))
    z0 = dst(w, Am2, [nb], 'iffalsed', '%s = 0' % IFB('m', 'n'))
    se2 = dst(w, An2, [z0], 'sumeq2dv', '%s = sum_ m e. %s 0' % (SM, RJ))
    sz = ap(w, An2, 'sumz', [dst(w, An2, [a1(w, An2, 'fzofi', '%s e. Fin' % RJ)], 'olcd', '( %s C_ ( ZZ>= ` 0 ) \\/ %s e. Fin )' % (RJ, RJ))], 'sum_ m e. %s 0 = 0' % RJ)
    t2 = dst(w, An2, [w.s([], 'simpr', '( %s -> -. D < n )' % An2)], 'iffalsed', '%s = 0' % TT('n'))
    case2 = dst(w, An2, [eqt(w, An2, se2, sz), t2], 'eqtr4d', '%s = %s' % (SM, TT('n')))
    pern = dst(w, An, [case1, case2], 'pm2.61dan', '%s = %s' % (SM, TT('n')))
    s1 = dst(w, A, [pern], 'sumeq2dv', 'sum_ n e. %s %s = %s' % (R, SM, TRUNC))
    eqt(w, A, eqc(w, A, s1), eqc(w, A, com))
    return fin(w)


def ld1cjk0():
    w = W('ld1cjk0', 'Lean ` coeffJK_eq_zero_of_not_block ` : the coefficient vanishes off its block (~ 3simpa , ~ iffalsed ).')
    COND = '( %s /\\ N <_ %s )' % (BLKC('J', 'N')[2:-2], NMAX)
    cond = '( %s < N /\\ N <_ ( ( 2 ^ ( J + 1 ) ) x. D ) /\\ N <_ %s )' % (NB('J'), NMAX)
    s1 = w.s([], '3simpa', '( %s -> %s )' % (cond, BLKC('J', 'N')))
    s2 = w.s([s1], 'con3i', '( -. %s -> -. %s )' % (BLKC('J', 'N'), cond))
    w.s([s2], 'iffalsed', '( -. %s -> %s = 0 )' % (BLKC('J', 'N'), COEFF('J', 'K', 'N')))
    return fin(w)


def cjk0x(w, A, notmem, X, xz, which):
    """( A -> COEFF = 0 ) from ( A -> -. N e. ( 1 ... X ) ) with X e. ZZ (xz); which = 2 (block range) or 3 (NMAX)"""
    P = parts(w, A)
    nn = P['N e. NN']
    nz = dst(w, A, [nn], 'nnzd', 'N e. ZZ')
    el = ap(w, A, 'elfz', [nz, a1(w, A, '1z', '1 e. ZZ'), xz], '( N e. ( 1 ... %s ) <-> ( 1 <_ N /\\ N <_ %s ) )' % (X, X))
    na = dst(w, A, [notmem, el], 'mtbid', '-. ( 1 <_ N /\\ N <_ %s )' % X)
    im = dst(w, A, [na, a1(w, A, 'imnan', '( ( 1 <_ N -> -. N <_ %s ) <-> -. ( 1 <_ N /\\ N <_ %s ) )' % (X, X))], 'mpbird', '( 1 <_ N -> -. N <_ %s )' % X)
    return dst(w, A, [dst(w, A, [nn], 'nnge1d', '1 <_ N'), im], 'mpd', '-. N <_ %s' % X)


def cond_of(J='J', N='N'):
    return '( %s < %s /\\ %s <_ ( ( 2 ^ ( %s + 1 ) ) x. D ) /\\ %s <_ %s )' % (NB(J), N, N, J, N, NMAX)


def ld1cjk0n():
    w = W('ld1cjk0n', 'Lean ` coeffJK_eq_zero_of_not_mem_Icc_Nmax ` : the coefficient vanishes beyond ` Nmax ` (~ elfz , ~ ceilcl ).')
    A = ante('ld1cjk0n'); P = parts(w, A)
    dr, z = P['D e. RR'], P['0 < D']
    rp = dst(w, A, [dr, z], 'elrpd', 'D e. RR+')
    c = Closure(w, A, {'D': [('RR+', rp), ('gt0', z)]})
    xz = ap(w, A, 'ceilcl', [c.mem('( ( 8 x. %s ) x. %s )' % (YP, L), 'RR')], '%s e. ZZ' % NMAX)
    nl = cjk0x(w, A, P['-. N e. %s' % FZN], NMAX, xz, 3)
    s1 = w.s([], 'simp3', '( %s -> N <_ %s )' % (cond_of(), NMAX))
    s2 = dst(w, A, [nl, w.s([s1], 'con3i', '( -. N <_ %s -> -. %s )' % (NMAX, cond_of()))], 'syl' if False else 'x', 'x') if False else w.s([nl, w.s([s1], 'con3i', '( -. N <_ %s -> -. %s )' % (NMAX, cond_of()))], 'syl', '( %s -> -. %s )' % (A, cond_of()))
    dst(w, A, [s2], 'iffalsed', '%s = 0' % COEFF('J', 'K', 'N'))
    return fin(w)


def ld1cjk0b():
    w = W('ld1cjk0b', 'Lean ` coeffJK_eq_zero_of_not_mem_blockRange ` : the coefficient vanishes off ` blockRange ` (~ elfz , ~ ceilge ).')
    A = ante('ld1cjk0b'); P = parts(w, A)
    dr, z, jn, nn = P['D e. RR'], P['0 < D'], P['J e. NN0'], P['N e. NN']
    rp = dst(w, A, [dr, z], 'elrpd', 'D e. RR+')
    c = Closure(w, A, {'D': [('RR+', rp), ('gt0', z)], 'J': ('NN0', jn), 'N': ('NN', nn)})
    X2 = '( ( 2 ^ ( J + 1 ) ) x. D )'; CX = '( |^ ` %s )' % X2
    xr = c.mem(X2, 'RR')
    xz = ap(w, A, 'ceilcl', [xr], '%s e. ZZ' % CX)
    nl = cjk0x(w, A, P['-. N e. %s' % BLK('J')], CX, xz, 2)
    ge = ap(w, A, 'ceilge', [xr], '%s <_ %s' % (X2, CX))
    A1 = '( %s /\\ N <_ %s )' % (A, X2)
    imp = dst(w, A, [dst(w, A1, [lift(w, c.mem('N', 'RR'), A1), lift(w, xr, A1), lift(w, dst(w, A, [xz], 'zred', '%s e. RR' % CX), A1), w.s([], 'simpr', '( %s -> N <_ %s )' % (A1, X2)), lift(w, ge, A1)], 'letrd', 'N <_ %s' % CX)], 'ex', '( N <_ %s -> N <_ %s )' % (X2, CX))
    nl2 = dst(w, A, [nl, imp], 'mtod', '-. N <_ %s' % X2)
    s1 = w.s([], 'simp2', '( %s -> N <_ %s )' % (cond_of(), X2))
    s2 = w.s([nl2, w.s([s1], 'con3i', '( -. N <_ %s -> -. %s )' % (X2, cond_of()))], 'syl', '( %s -> -. %s )' % (A, cond_of()))
    dst(w, A, [s2], 'iffalsed', '%s = 0' % COEFF('J', 'K', 'N'))
    return fin(w)


def coeffcl(w, An, c, n, k='K'):
    """closure facts for COEFF(J,k,n,T) e. RR under An (needs n NN, D RR+, J NN0, k NN0, T RR, YP RR+)"""
    c.leaf('( -u ( log ` ( %s / %s ) ) ^ %s )' % (n, NB('J'), k), 'RR', c.mem('( -u ( log ` ( %s / %s ) ) ^ %s )' % (n, NB('J'), k), 'RR'))
    return c.mem(COEFF('J', k, n), 'RR')


def ld1tayeq():
    w = W('ld1tayeq', 'Lean ` taylorSum_eq_blockRange ` (audit F1): the Taylor component over ` ( 1 ... Nmax ) ` equals the sum over ` blockRange ` , both ranges containing the support of ` coeffJK ` (~ fsumss , ~ ld1cjk0n , ~ ld1cjk0b ).')
    A = ante('ld1tayeq'); P, c, F = setupx(w, A)
    jn, kn, gr, tr = P['J e. NN0'], P['K e. NN0'], P['G e. RR'], P['T e. RR']
    h0, rp3 = hab(w, A, F)
    BJ = BLK('J'); I = '( %s i^i %s )' % (FZN, BJ)
    f = lambda n: TSUMMAND('J', 'K', n, 'G', 'T')
    facts = basefacts(F) + [('J', 'NN0', jn), ('K', 'NN0', kn), ('G', 'RR', gr), ('T', 'RR', tr), ('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC'))]
    def fcl(An, nst):
        cn = liftcl(w, A, An, facts); termcl(w, An, cn, 'n', nst, F, rp3)
        coeffcl(w, An, cn, 'n')
        return cn, cn.mem(f('n'), 'CC')
    AI = '( %s /\\ n e. %s )' % (A, I)
    nI = w.s([], 'simpr', '( %s -> n e. %s )' % (AI, I))
    nI1 = ap(w, AI, 'elinel1', [nI], 'n e. %s' % FZN)
    _, fI = fcl(AI, ap(w, AI, 'elfznn', [nI1], 'n e. NN'))
    def zero(Bset, X, sub_lemma, other, which):
        """( ( A /\\ n e. ( Bset \\ I ) ) -> f = 0 )"""
        Ad = '( %s /\\ n e. ( %s \\ %s ) )' % (A, Bset, I)
        nd = w.s([], 'simpr', '( %s -> n e. ( %s \\ %s ) )' % (Ad, Bset, I))
        inB = dst(w, Ad, [nd], 'eldifad', 'n e. %s' % Bset)
        notI = dst(w, Ad, [nd], 'eldifbd', '-. n e. %s' % I)
        elin = a1(w, Ad, 'elin', '( n e. %s <-> ( n e. %s /\\ n e. %s ) )' % (I, FZN, BJ))
        na = dst(w, Ad, [notI, elin], 'mtbid', '-. ( n e. %s /\\ n e. %s )' % (FZN, BJ))
        if which == 'fz':   # n e. FZN known, conclude -. n e. BJ
            im = dst(w, Ad, [na, a1(w, Ad, 'imnan', '( ( n e. %s -> -. n e. %s ) <-> -. ( n e. %s /\\ n e. %s ) )' % (FZN, BJ, FZN, BJ))], 'mpbird', '( n e. %s -> -. n e. %s )' % (FZN, BJ))
            notx = dst(w, Ad, [inB, im], 'mpd', '-. n e. %s' % BJ)
            lem = 'ld1cjk0b'
        else:               # n e. BJ known, conclude -. n e. FZN
            im = dst(w, Ad, [na, a1(w, Ad, 'pm3.2' if False else 'x', 'x') if False else na], 'x', 'x') if False else None
            # -. ( a /\ b ) with b: -. a  via  ( b -> -. a ) <-> -. ( b /\ a ) after ancom
            na2 = dst(w, Ad, [na, a1(w, Ad, 'ancom', '( ( n e. %s /\\ n e. %s ) <-> ( n e. %s /\\ n e. %s ) )' % (FZN, BJ, BJ, FZN))], 'mtbid', '-. ( n e. %s /\\ n e. %s )' % (BJ, FZN))
            im = dst(w, Ad, [na2, a1(w, Ad, 'imnan', '( ( n e. %s -> -. n e. %s ) <-> -. ( n e. %s /\\ n e. %s ) )' % (BJ, FZN, BJ, FZN))], 'mpbird', '( n e. %s -> -. n e. %s )' % (BJ, FZN))
            notx = dst(w, Ad, [inB, im], 'mpd', '-. n e. %s' % FZN)
            lem = 'ld1cjk0n'
        nN = ap(w, Ad, 'elfznn', [inB], 'n e. NN')
        cd = liftcl(w, A, Ad, facts); termcl(w, Ad, cd, 'n', nN, F, rp3)
        z = ap(w, Ad, lem, [J(w, Ad, J(w, Ad, lift(w, F['dr'], Ad), lift(w, F['z'], Ad)), J(w, Ad, lift(w, jn, Ad), nN), notx)], '%s = 0' % COEFF('J', 'K', 'n'))
        m1 = dst(w, Ad, [dst(w, Ad, [z], 'oveq1d', '( %s x. ( C ` n ) ) = ( 0 x. ( C ` n ) )' % COEFF('J', 'K', 'n')), dst(w, Ad, [cd.mem('( C ` n )', 'CC')], 'mul02d', '( 0 x. ( C ` n ) ) = 0')], 'eqtrd', '( %s x. ( C ` n ) ) = 0' % COEFF('J', 'K', 'n'))
        NX = NEX('n', 'G')
        return dst(w, Ad, [dst(w, Ad, [m1], 'oveq1d', '%s = ( 0 x. %s )' % (f('n'), NX)), dst(w, Ad, [cd.mem(NX, 'CC')], 'mul02d', '( 0 x. %s ) = 0' % NX)], 'eqtrd', '%s = 0' % f('n'))
    z1 = zero(FZN, None, None, None, 'fz')
    z2 = zero(BJ, None, None, None, 'bj')
    s1 = w.s([a1(w, A, 'inss1', '%s C_ %s' % (I, FZN)), fI, z1, dst(w, A, [], 'fzfid', '%s e. Fin' % FZN)], 'fsumss', '( %s -> sum_ n e. %s %s = sum_ n e. %s %s )' % (A, I, f('n'), FZN, f('n')))
    s2 = w.s([a1(w, A, 'inss2', '%s C_ %s' % (I, BJ)), fI, z2, dst(w, A, [], 'fzfid', '%s e. Fin' % BJ)], 'fsumss', '( %s -> sum_ n e. %s %s = sum_ n e. %s %s )' % (A, I, f('n'), BJ, f('n')))
    dst(w, A, [s1, s2], 'eqtr3d', '%s = %s' % (TAYSUM('J', 'K', 'G'), TWIST('J', 'K', 'G')))
    return fin(w)


def ld1rpowtay():
    w = W('ld1rpowtay', 'Lean ` rpow_neg_eq_taylor ` : ` n ^ -u ( sigma + delta ) = N ^ -u delta n ^ -u sigma ( sum_ ( k <_ J ) delta ^ k ( -u log ( n / N ) ) ^ k / k ! + r ) ` (~ cxpefd , ~ relogdivd , ~ efadd ).')
    A = ante('ld1rpowtay'); P = parts(w, A)
    brp, nn, tr, er, jn = P['B e. RR+'], P['N e. NN'], P['T e. RR'], P['E e. RR'], P['J e. NN0']
    nrp = dst(w, A, [nn], 'nnrpd', 'N e. RR+')
    lB = '( log ` B )'; lN = '( log ` N )'
    c = Closure(w, A, {'B': ('RR+', brp), 'N': ('RR+', nrp), 'T': ('RR', tr), 'E': ('RR', er), 'J': ('NN0', jn),
                       lB: ('RR', dst(w, A, [brp], 'relogcld', '%s e. RR' % lB)), lN: ('RR', dst(w, A, [nrp], 'relogcld', '%s e. RR' % lN))})
    LR = LOGR('N', 'B')
    ld = dst(w, A, [dst(w, A, [nrp, brp], 'relogdivd', '( log ` ( N / B ) ) = ( %s - %s )' % (lN, lB))], 'negeqd', '%s = -u ( %s - %s )' % (LR, lN, lB))
    c.leaf(LR, 'RR', c.mem(LR, 'RR'))
    Pk = TPOLY('E', 'B', 'J', 'N'); R = TREM('E', 'B', 'J', 'N'); EXR = '( exp ` ( E x. %s ) )' % LR
    Ak = '( %s /\\ k e. ( 0 ... J ) )' % A
    ck = Closure(w, Ak, {'E': ('RR', lift(w, er, Ak)), LR: ('RR', lift(w, c.mem(LR, 'RR'), Ak)), 'k': ('NN0', ap(w, Ak, 'elfznn0', [w.s([], 'simpr', '( %s -> k e. ( 0 ... J ) )' % Ak)], 'k e. NN0'))})
    ck.leaf('( ! ` k )', 'NN', dst(w, Ak, [ck.mem('k', 'NN0')], 'faccld', '( ! ` k ) e. NN'))
    pc = dst(w, A, [dst(w, A, [], 'fzfid', '( 0 ... J ) e. Fin'), ck.mem('( ( ( E ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % LR, 'CC')], 'fsumcl', '%s e. CC' % Pk)
    c.leaf(Pk, 'CC', pc)
    pr = dst(w, A, [pc, c.mem(EXR, 'CC')], 'pncan3d', '( %s + %s ) = %s' % (Pk, R, EXR))
    nc = c.mem('N', 'CC'); n0 = c.ne0('N'); bc = c.mem('B', 'CC'); b0 = c.ne0('B')
    X0 = '( -u ( T + E ) x. %s )' % lN; X1 = '( -u E x. %s )' % lB; X2 = '( -u T x. %s )' % lN; X3 = '( E x. %s )' % LR
    e1 = dst(w, A, [nc, n0, c.mem('-u ( T + E )', 'CC')], 'cxpefd', '( N ^c -u ( T + E ) ) = ( exp ` %s )' % X0)
    e2 = dst(w, A, [bc, b0, c.mem('-u E', 'CC')], 'cxpefd', '( B ^c -u E ) = ( exp ` %s )' % X1)
    e3 = dst(w, A, [nc, n0, c.mem('-u T', 'CC')], 'cxpefd', '( N ^c -u T ) = ( exp ` %s )' % X2)
    RHS = '( ( B ^c -u E ) x. ( ( N ^c -u T ) x. ( %s + %s ) ) )' % (Pk, R)
    r1 = dst(w, A, [e2, dst(w, A, [e3, pr], 'oveq12d', '( ( N ^c -u T ) x. ( %s + %s ) ) = ( ( exp ` %s ) x. %s )' % (Pk, R, X2, EXR))], 'oveq12d', '%s = ( ( exp ` %s ) x. ( ( exp ` %s ) x. %s ) )' % (RHS, X1, X2, EXR))
    ea1 = eqc(w, A, ap(w, A, 'efadd', [c.mem(X2, 'CC'), c.mem(X3, 'CC')], '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. %s )' % (X2, X3, X2, EXR)))
    ea2 = eqc(w, A, ap(w, A, 'efadd', [c.mem(X1, 'CC'), c.mem('( %s + %s )' % (X2, X3), 'CC')], '( exp ` ( %s + ( %s + %s ) ) ) = ( ( exp ` %s ) x. ( exp ` ( %s + %s ) ) )' % (X1, X2, X3, X1, X2, X3)))
    r2 = eqt(w, A, dst(w, A, [ea1], 'oveq2d', '( ( exp ` %s ) x. ( ( exp ` %s ) x. %s ) ) = ( ( exp ` %s ) x. ( exp ` ( %s + %s ) ) )' % (X1, X2, EXR, X1, X2, X3)), ea2)
    SUMX = '( %s + ( %s + %s ) )' % (X1, X2, X3)
    sub = dst(w, A, [dst(w, A, [dst(w, A, [ld], 'oveq2d', '%s = ( E x. -u ( %s - %s ) )' % (X3, lN, lB))], 'oveq2d', '( %s + %s ) = ( %s + ( E x. -u ( %s - %s ) ) )' % (X2, X3, X2, lN, lB))], 'oveq2d',
              '%s = ( %s + ( %s + ( E x. -u ( %s - %s ) ) ) )' % (SUMX, X1, X2, lN, lB))
    rg = ringeq(w, A, '( %s + ( %s + ( E x. -u ( %s - %s ) ) ) )' % (X1, X2, lN, lB), X0, c)
    r3 = dst(w, A, [eqt(w, A, sub, rg)], 'fveq2d', '( exp ` %s ) = ( exp ` %s )' % (SUMX, X0))
    dst(w, A, [e1, eqt(w, A, eqt(w, A, r1, r2), r3)], 'eqtr4d', '( N ^c -u ( T + E ) ) = %s' % RHS)
    return fin(w)


if __name__ == '__main__':
    for lab in ['ld1ncov', 'ld1exblk', 'ld1blku', 'ld1sblk', 'ld1cjk0', 'ld1cjk0n', 'ld1cjk0b', 'ld1tayeq', 'ld1rpowtay']:
        if want(lab):
            if not globals()[lab]():
                sys.exit(1)
