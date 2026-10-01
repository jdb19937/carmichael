"""ZL1 section A: a set.mm Dirichlet character read on NN (zl1cxv, zl1chrb), the
principal character (zl1prn), and the mean-free partial sums of every character
(zl1blk .. zl1aagr): C5's chrblk / chrsper / chrsmod / chrsbnd / lchrcsf /
lchrhol0 / lchragr re-run on X ( i ) - q."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl1lib import *
from zl1lib import mptval_ as mptval
from cl import Closure

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    return w.run()


WIF = '( 0 ..^ N )'
WI = 'if ( N = 0 , ZZ , %s )' % WIF
CHV_ = CHV


def nxctx(w, A1, nx):
    d = {'nx': nx}
    d['nn'] = w.s([nx, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A1)
    d['xd'] = w.s([nx, w.inst('simpr')], 'syl', '( %s -> X e. %s )' % (A1, DC))
    d['g'], d['z'], d['b'], d['l'] = dchyp(w)
    d['bb'] = w.s([], 'eqid', '%s = %s' % (BZ, BZ))
    d['nn0'] = w.s([d['nn']], 'nnnn0d', '( %s -> N e. NN0 )' % A1)
    d['nz'] = w.s([d['nn']], 'nnzd', '( %s -> N e. ZZ )' % A1)
    return d


def chvcl(w, ante, K, nx, mk):
    return w.s([w.s([nx, mk], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ %s e. NN ) )' % (ante, DC, K)), w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (ante, CHV(K)))


def qmcl(w, ante, nn):
    """( ante -> QM e. CC ) from nn: ( ante -> N e. NN )"""
    pc = w.s([w.s([w.s([nn, w.inst('phicl')], 'syl', '( %s -> ( phi ` N ) e. NN )' % ante)], 'nncnd', '( %s -> ( phi ` N ) e. CC )' % ante),
              w.s([nn], 'nncnd', '( %s -> N e. CC )' % ante), w.s([nn], 'nnne0d', '( %s -> N =/= 0 )' % ante)], 'divcld', '( %s -> ( ( phi ` N ) / N ) e. CC )' % ante)
    return w.s([pc, a1(w, ante, '0cn', '0 e. CC')], 'ifcld', '( %s -> %s e. CC )' % (ante, QM))


def chwcl(w, ante, K, nx, mk, nn):
    return w.s([chvcl(w, ante, K, nx, mk), qmcl(w, ante, nn)], 'subcld', '( %s -> %s e. CC )' % (ante, CHW(K)))


# ---------------------------------------------------------------- zl1cxv
if not only or 'zl1cxv' in only:
    w = W('zl1cxv', 'The value of a Dirichlet character read on the positive integers through ` ZRHom ` .')
    A0 = '( %s /\\ K e. NN )' % NX
    kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
    st, _ = mptval(w, A0, 'a', 'NN', CHV('a'), 'K', kn, mp=CX, name='qed', closure=None, exs=w.s([], 'fvexd', '( %s -> %s e. _V )' % (A0, CHV('K'))))
    go(w)


def cxv(w, ante, K, nx, mk):
    return w.s([w.s([nx, mk], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (ante, NX, K)), w.inst('zl1cxv')], 'syl', '( %s -> ( %s ` %s ) = %s )' % (ante, CX, K, CHV(K)))


# ---------------------------------------------------------------- zl1chrb
if not only or 'zl1chrb' in only:
    w = W('zl1chrb', 'A Dirichlet character read on the positive integers satisfies the character facts ` CHRB ` '
          'of ~ z6dlbz : a completely multiplicative map ` NN --> CC ` with ` C ( 1 ) = 1 ` and ` | C | <_ 1 ` '
          '(Lean ` MulChar.map_one ` , ` map_mul ` , ` DirichletCharacter.norm_le_one ` ; ~ dchrzrh1 , ~ dchrzrhmul , ~ lchrabs ).')
    A0 = NX
    nx = w.s([], 'id', '( %s -> %s )' % (A0, NX))
    d = nxctx(w, A0, nx)
    Aa = '( %s /\\ a e. NN )' % A0
    fm = w.s([chvcl(w, Aa, 'a', w.s([], 'simpl', '( %s -> %s )' % (Aa, NX)), w.s([], 'simpr', '( %s -> a e. NN )' % Aa)), w.s([], 'eqid', '%s = %s' % (CX, CX))], 'fmptd',
             '( %s -> %s : NN --> CC )' % (A0, CX))
    one = w.s([cxv(w, A0, '1', nx, a1(w, A0, '1nn', '1 e. NN')), w.s([d['g'], d['z'], d['b'], d['l'], d['xd']], 'dchrzrh1', '( %s -> %s = 1 )' % (A0, CHV('1')))], 'eqtrd',
              '( %s -> ( %s ` 1 ) = 1 )' % (A0, CX))
    Aij = '( %s /\\ ( i e. NN /\\ j e. NN ) )' % A0
    inn = w.s([], 'simprl', '( %s -> i e. NN )' % Aij)
    jnn = w.s([], 'simprr', '( %s -> j e. NN )' % Aij)
    nxij = w.s([], 'simpl', '( %s -> %s )' % (Aij, NX))
    dij = nxctx(w, Aij, nxij)
    ijn = w.s([inn, jnn], 'nnmulcld', '( %s -> ( i x. j ) e. NN )' % Aij)
    mul = w.s([dij['g'], dij['z'], dij['b'], dij['l'], dij['xd'], w.s([inn], 'nnzd', '( %s -> i e. ZZ )' % Aij), w.s([jnn], 'nnzd', '( %s -> j e. ZZ )' % Aij)], 'dchrzrhmul',
              '( %s -> %s = ( %s x. %s ) )' % (Aij, CHV('( i x. j )'), CHV('i'), CHV('j')))
    m1 = chain(w, Aij, ['( %s ` ( i x. j ) )' % CX, CHV('( i x. j )'), '( %s x. %s )' % (CHV('i'), CHV('j')), '( ( %s ` i ) x. ( %s ` j ) )' % (CX, CX)],
               [cxv(w, Aij, '( i x. j )', nxij, ijn), mul,
                ('r', E(w, Aij, 'oveq12d', [cxv(w, Aij, 'i', nxij, inn), cxv(w, Aij, 'j', nxij, jnn)], '( ( %s ` i ) x. ( %s ` j ) )' % (CX, CX), '( %s x. %s )' % (CHV('i'), CHV('j'))))])
    mr = w.s([m1], 'ralrimivva', '( %s -> A. i e. NN A. j e. NN ( %s ` ( i x. j ) ) = ( ( %s ` i ) x. ( %s ` j ) ) )' % (A0, CX, CX, CX))
    Aj = '( %s /\\ j e. NN )' % A0
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    nxj = w.s([], 'simpl', '( %s -> %s )' % (Aj, NX))
    ab = w.s([w.s([cxv(w, Aj, 'j', nxj, jn)], 'fveq2d', '( %s -> ( abs ` ( %s ` j ) ) = ( abs ` %s ) )' % (Aj, CX, CHV('j'))),
              w.s([w.s([nxj, jn], 'jca', '( %s -> ( %s /\\ j e. NN ) )' % (Aj, NX)), w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (Aj, CHV('j')))], 'eqbrtrd',
             '( %s -> ( abs ` ( %s ` j ) ) <_ 1 )' % (Aj, CX))
    abr = w.s([ab], 'ralrimiva', '( %s -> A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 )' % (A0, CX))
    CHRX = '( %s : NN --> CC /\\ ( %s ` 1 ) = 1 /\\ A. i e. NN A. j e. NN ( %s ` ( i x. j ) ) = ( ( %s ` i ) x. ( %s ` j ) ) )' % (CX, CX, CX, CX, CX)
    w.qed([w.s([fm, one, mr], '3jca', '( %s -> %s )' % (A0, CHRX)), abr], 'jca', '( %s -> %s )' % (A0, CHRBX))
    go(w)

UN = '( Unit ` %s )' % ZN


def onecl(w, ante, nn):
    """( ante -> ONE e. DC )"""
    g = w.s([], 'eqid', '%s = %s' % (GG, GG))
    ab = w.s([nn, w.s([g], 'dchrabl', '( N e. NN -> %s e. Abel )' % GG)], 'syl', '( %s -> %s e. Abel )' % (ante, GG))
    gr = w.s([ab, w.inst('ablgrp')], 'syl', '( %s -> %s e. Grp )' % (ante, GG))
    return w.s([gr, w.s([w.s([], 'eqid', '%s = %s' % (DC, DC)), w.s([], 'eqid', '%s = %s' % (ONE, ONE))], 'grpidcl', '( %s e. Grp -> %s e. %s )' % (GG, ONE, DC))], 'syl',
               '( %s -> %s e. %s )' % (ante, ONE, DC))


def unit(w, ante, A, nn0, az):
    """( ante -> ( ( LH ` A ) e. U <-> ( A gcd N ) = 1 ) )"""
    zn = w.s([], 'eqid', '%s = %s' % (ZN, ZN)); u = w.s([], 'eqid', '%s = %s' % (UN, UN)); l = w.s([], 'eqid', '%s = %s' % (LH, LH))
    return w.s([nn0, az, w.s([zn, u, l], 'znunit', '( ( N e. NN0 /\\ %s e. ZZ ) -> ( ( %s ` %s ) e. %s <-> ( %s gcd N ) = 1 ) )' % (A, LH, A, UN, A))], 'syl2anc',
               '( %s -> ( ( %s ` %s ) e. %s <-> ( %s gcd N ) = 1 ) )' % (ante, LH, A, UN, A))


def one1(w, ante, A, nn, au):
    """( ante -> ( ONE ` ( LH ` A ) ) = 1 ) from au: ( ante -> ( LH ` A ) e. U )"""
    g = w.s([], 'eqid', '%s = %s' % (GG, GG)); zn = w.s([], 'eqid', '%s = %s' % (ZN, ZN))
    o = w.s([], 'eqid', '%s = %s' % (ONE, ONE)); u = w.s([], 'eqid', '%s = %s' % (UN, UN))
    return w.s([g, zn, o, u, nn, au], 'dchr1', '( %s -> ( %s ` ( %s ` %s ) ) = 1 )' % (ante, ONE, LH, A))


# ---------------------------------------------------------------- zl1prn
if not only or 'zl1prn' in only:
    w = W('zl1prn', 'A Dirichlet character read on the positive integers is the principal indicator ` PRN ` '
          'exactly when it is the trivial character (Lean ` DirichletCharacter.eq_one_iff ` ; ~ dchreqz , ~ dchr1 , ~ dchrn0 , ~ znunit ).')
    A0 = NX
    # ->
    A1 = '( %s /\\ %s = %s )' % (NX, CX, PRN)
    nx1 = w.s([], 'simpl', '( %s -> %s )' % (A1, NX))
    d1 = nxctx(w, A1, nx1)
    Aa = '( ( %s /\\ y e. ZZ ) /\\ ( y gcd N ) = 1 )' % A1
    az = w.s([], 'simplr', '( %s -> y e. ZZ )' % Aa)
    ag = w.s([], 'simpr', '( %s -> ( y gcd N ) = 1 )' % Aa)
    nxa = w.s([nx1], 'ad2antrr', '( %s -> %s )' % (Aa, NX))
    da = nxctx(w, Aa, nxa)
    AM = '( y mod N )'; B = '( %s + N )' % AM
    amn = w.s([az, da['nn'], w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (Aa, AM))
    bn = w.s([amn, da['nn'], w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> %s e. NN )' % (Aa, B))
    bz = w.s([bn], 'nnzd', '( %s -> %s e. ZZ )' % (Aa, B))
    nrp = w.s([da['nn']], 'nnrpd', '( %s -> N e. RR+ )' % Aa)
    amr = w.s([amn], 'nn0red', '( %s -> %s e. RR )' % (Aa, AM))
    bb1 = E(w, Aa, 'oveq2d', [w.s([w.s([da['nn']], 'nncnd', '( %s -> N e. CC )' % Aa)], 'mullidd', '( %s -> ( 1 x. N ) = N )' % Aa)], '( %s + ( 1 x. N ) )' % AM, B)
    mc = w.s([amr, nrp, a1(w, Aa, '1z', '1 e. ZZ'), w.inst('modcyc')], 'syl3anc', '( %s -> ( ( %s + ( 1 x. N ) ) mod N ) = ( %s mod N ) )' % (Aa, AM, AM))
    ma = w.s([w.s([az], 'zred', '( %s -> y e. RR )' % Aa), nrp, w.inst('modabs2')], 'syl2anc', '( %s -> ( %s mod N ) = %s )' % (Aa, AM, AM))
    bm = chain(w, Aa, ['( %s mod N )' % B, '( ( %s + ( 1 x. N ) ) mod N )' % AM, '( %s mod N )' % AM, AM],
               [('r', E(w, Aa, 'oveq1d', [bb1], '( ( %s + ( 1 x. N ) ) mod N )' % AM, '( %s mod N )' % B)), mc, ma])
    # X ( L a ) = X ( L b )
    x1 = w.s([w.s([nxa, az], 'jca', '( %s -> ( %s /\\ y e. ZZ ) )' % (Aa, NX)), w.inst('dchrzrhmod')], 'syl', '( %s -> %s = %s )' % (Aa, CHV(AM), CHV('y')))
    x2 = w.s([w.s([nxa, bz], 'jca', '( %s -> ( %s /\\ %s e. ZZ ) )' % (Aa, NX, B)), w.inst('dchrzrhmod')], 'syl', '( %s -> %s = %s )' % (Aa, CHV('( %s mod N )' % B), CHV(B)))
    x3 = w.s([w.s([w.s([bm], 'fveq2d', '( %s -> ( %s ` ( %s mod N ) ) = ( %s ` %s ) )' % (Aa, LH, B, LH, AM))], 'fveq2d',
                  '( %s -> %s = %s )' % (Aa, CHV('( %s mod N )' % B), CHV(AM)))], 'idi', '( %s -> %s = %s )' % (Aa, CHV('( %s mod N )' % B), CHV(AM)))
    xab = chain(w, Aa, [CHV('y'), CHV(AM), CHV('( %s mod N )' % B), CHV(B)], [('r', x1), ('r', x3), x2])
    # X ( L b ) = CX ( b ) = PRN ( b ) = 1
    gb = chain(w, Aa, ['( %s gcd N )' % B, '( ( %s mod N ) gcd N )' % B, '( %s gcd N )' % AM, '( y gcd N )', '1'],
               [('r', w.s([bz, da['nn'], w.inst('modgcd')], 'syl2anc', '( %s -> ( ( %s mod N ) gcd N ) = ( %s gcd N ) )' % (Aa, B, B))),
                E(w, Aa, 'oveq1d', [bm], '( ( %s mod N ) gcd N )' % B, '( %s gcd N )' % AM),
                w.s([az, da['nn'], w.inst('modgcd')], 'syl2anc', '( %s -> ( %s gcd N ) = ( y gcd N ) )' % (Aa, AM)), ag])
    pv, _ = mptv(w, Aa, 'n', 'NN', 'if ( ( n gcd N ) = 1 , 1 , 0 )', B, bn, mp=PRN,
                   exs=w.s([w.s([a1(w, Aa, '1ex', '1 e. _V'), a1(w, Aa, 'c0ex', '0 e. _V')], 'ifcld', '( %s -> if ( ( %s gcd N ) = 1 , 1 , 0 ) e. _V )' % (Aa, B))], 'idi',
                           '( %s -> if ( ( %s gcd N ) = 1 , 1 , 0 ) e. _V )' % (Aa, B)))
    it = w.s([gb], 'iftrued', '( %s -> if ( ( %s gcd N ) = 1 , 1 , 0 ) = 1 )' % (Aa, B))
    cp = w.s([w.s([], 'simpr', '( %s -> %s = %s )' % (A1, CX, PRN))], 'ad2antrr', '( %s -> %s = %s )' % (Aa, CX, PRN))
    cpb = w.s([cp], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (Aa, CX, B, PRN, B))
    xb1 = chain(w, Aa, [CHV(B), '( %s ` %s )' % (CX, B), '( %s ` %s )' % (PRN, B), 'if ( ( %s gcd N ) = 1 , 1 , 0 )' % B, '1'],
                [('r', cxv(w, Aa, B, nxa, bn)), cpb, pv, it])
    au = w.s([ag, unit(w, Aa, 'y', da['nn0'], az)], 'mpbird', '( %s -> ( %s ` y ) e. %s )' % (Aa, LH, UN))
    o1 = one1(w, Aa, 'y', da['nn'], au)
    xeq = chain(w, Aa, [CHV('y'), CHV(B), '1', '( %s ` ( %s ` y ) )' % (ONE, LH)], [xab, xb1, ('r', o1)])
    rr = w.s([w.s([xeq], 'ex', '( ( %s /\\ y e. ZZ ) -> ( ( y gcd N ) = 1 -> %s = ( %s ` ( %s ` y ) ) ) )' % (A1, CHV('y'), ONE, LH))], 'ralrimiva',
             '( %s -> A. y e. ZZ ( ( y gcd N ) = 1 -> %s = ( %s ` ( %s ` y ) ) ) )' % (A1, CHV('y'), ONE, LH))
    eqz = w.s([w.s([d1['nn'], d1['xd'], onecl(w, A1, d1['nn'])], '3jca', '( %s -> ( N e. NN /\\ X e. %s /\\ %s e. %s ) )' % (A1, DC, ONE, DC)), w.inst('dchreqz')], 'syl',
              '( %s -> ( X = %s <-> A. y e. ZZ ( ( y gcd N ) = 1 -> %s = ( %s ` ( %s ` y ) ) ) ) )' % (A1, ONE, CHV('y'), ONE, LH))
    fwd = w.s([rr, eqz], 'mpbird', '( %s -> X = %s )' % (A1, ONE))
    # <-
    A2 = '( %s /\\ X = %s )' % (NX, ONE)
    nx2 = w.s([], 'simpl', '( %s -> %s )' % (A2, NX))
    Ab = '( %s /\\ a e. NN )' % A2
    an = w.s([], 'simpr', '( %s -> a e. NN )' % Ab)
    nxb = w.s([nx2], 'adantr', '( %s -> %s )' % (Ab, NX))
    db = nxctx(w, Ab, nxb)
    xo = w.s([w.s([w.s([], 'simpr', '( %s -> X = %s )' % (A2, ONE))], 'adantr', '( %s -> X = %s )' % (Ab, ONE))], 'fveq1d',
             '( %s -> %s = ( %s ` ( %s ` a ) ) )' % (Ab, CHV('a'), ONE, LH))
    uab = unit(w, Ab, 'a', db['nn0'], w.s([an], 'nnzd', '( %s -> a e. ZZ )' % Ab))
    IFA = 'if ( ( a gcd N ) = 1 , 1 , 0 )'
    Ay = '( %s /\\ ( a gcd N ) = 1 )' % Ab
    ya = w.s([w.s([], 'simpr', '( %s -> ( a gcd N ) = 1 )' % Ay), w.s([uab], 'adantr', '( %s -> ( ( %s ` a ) e. %s <-> ( a gcd N ) = 1 ) )' % (Ay, LH, UN, ))], 'mpbird',
             '( %s -> ( %s ` a ) e. %s )' % (Ay, LH, UN))
    cy = chain(w, Ay, ['( %s ` ( %s ` a ) )' % (ONE, LH), '1', IFA],
               [one1(w, Ay, 'a', w.s([db['nn']], 'adantr', '( %s -> N e. NN )' % Ay), ya),
                ('r', w.s([w.s([], 'simpr', '( %s -> ( a gcd N ) = 1 )' % Ay)], 'iftrued', '( %s -> %s = 1 )' % (Ay, IFA)))])
    An_ = '( %s /\\ -. ( a gcd N ) = 1 )' % Ab
    nu_ = w.s([w.s([], 'simpr', '( %s -> -. ( a gcd N ) = 1 )' % An_), w.s([uab], 'adantr', '( %s -> ( ( %s ` a ) e. %s <-> ( a gcd N ) = 1 ) )' % (An_, LH, UN))], 'mtbird',
              '( %s -> -. ( %s ` a ) e. %s )' % (An_, LH, UN))
    zn = w.s([], 'eqid', '%s = %s' % (ZN, ZN))
    lf = w.s([w.s([w.s([db['nn0']], 'adantr', '( %s -> N e. NN0 )' % An_), w.s([zn, db['bb'], db['l']], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> %s )' % (LH, BZ))], 'syl',
                  '( %s -> %s : ZZ -onto-> %s )' % (An_, LH, BZ)), w.inst('fof')], 'syl', '( %s -> %s : ZZ --> %s )' % (An_, LH, BZ))
    lab = w.s([lf, w.s([w.s([an], 'adantr', '( %s -> a e. NN )' % An_)], 'nnzd', '( %s -> a e. ZZ )' % An_)], 'ffvelcdmd', '( %s -> ( %s ` a ) e. %s )' % (An_, LH, BZ))
    g_, z_, d_, l_ = dchyp(w)
    n0 = w.s([g_, z_, d_, db['bb'], w.s([], 'eqid', '%s = %s' % (UN, UN)), onecl(w, An_, w.s([db['nn']], 'adantr', '( %s -> N e. NN )' % An_)), lab], 'dchrn0',
             '( %s -> ( ( %s ` ( %s ` a ) ) =/= 0 <-> ( %s ` a ) e. %s ) )' % (An_, ONE, LH, LH, UN))
    nn0_ = w.s([nu_, n0], 'mtbird', '( %s -> -. ( %s ` ( %s ` a ) ) =/= 0 )' % (An_, ONE, LH))
    z0 = w.s([nn0_, w.s([], 'nne', '( -. ( %s ` ( %s ` a ) ) =/= 0 <-> ( %s ` ( %s ` a ) ) = 0 )' % (ONE, LH, ONE, LH))], 'sylib', '( %s -> ( %s ` ( %s ` a ) ) = 0 )' % (An_, ONE, LH))
    cn = chain(w, An_, ['( %s ` ( %s ` a ) )' % (ONE, LH), '0', IFA],
               [z0, ('r', w.s([w.s([], 'simpr', '( %s -> -. ( a gcd N ) = 1 )' % An_)], 'iffalsed', '( %s -> %s = 0 )' % (An_, IFA)))])
    oc = w.s([cy, cn], 'pm2.61dan', '( %s -> ( %s ` ( %s ` a ) ) = %s )' % (Ab, ONE, LH, IFA))
    pa = w.s([xo, oc], 'eqtrd', '( %s -> %s = %s )' % (Ab, CHV('a'), IFA))
    m1 = w.s([pa], 'mpteq2dva', '( %s -> %s = ( a e. NN |-> %s ) )' % (A2, CX, IFA))
    cb = w.s([w.s([w.s([w.s([], 'oveq1', '( a = n -> ( a gcd N ) = ( n gcd N ) )')], 'eqeq1d', '( a = n -> ( ( a gcd N ) = 1 <-> ( n gcd N ) = 1 ) )')], 'ifbid',
                  '( a = n -> %s = if ( ( n gcd N ) = 1 , 1 , 0 ) )' % IFA)], 'cbvmptv', '( a e. NN |-> %s ) = %s' % (IFA, PRN))
    bwd = w.s([m1, w.s([cb], 'a1i', '( %s -> ( a e. NN |-> %s ) = %s )' % (A2, IFA, PRN))], 'eqtrd', '( %s -> %s = %s )' % (A2, CX, PRN))
    w.qed([w.s([fwd], 'ex', '( %s -> ( %s = %s -> X = %s ) )' % (A0, CX, PRN, ONE)), w.s([bwd], 'ex', '( %s -> ( X = %s -> %s = %s ) )' % (A0, ONE, CX, PRN))], 'impbid',
          '( %s -> ( %s = %s <-> X = %s ) )' % (A0, CX, PRN, ONE))
    go(w)


# ---------------------------------------------------------------- zl1blk
if not only or 'zl1blk' in only:
    w = W('zl1blk', 'A Dirichlet character sums to ` if ( X = 1 , phi ( N ) , 0 ) ` over any block of ` N ` consecutive '
          'positive integers ( ~ dchrsum translated; C5\'s ~ chrblk without ` X =/= 1 ` ).')
    A0 = '( %s /\\ J e. NN0 )' % NX
    d = nxctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, NX)))
    jn0 = w.s([], 'simpr', '( %s -> J e. NN0 )' % A0)
    K = '( J + 1 )'
    kn = w.s([jn0, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A0, K))
    kz = w.s([kn], 'nnzd', '( %s -> %s e. ZZ )' % (A0, K))
    kc = w.s([kn], 'nncnd', '( %s -> %s e. CC )' % (A0, K))
    nc = w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % A0)
    one = a1(w, A0, 'ax-1cn', '1 e. CC')
    nm1 = w.s([d['nz'], a1(w, A0, '1z', '1 e. ZZ')], 'zsubcld', '( %s -> ( N - 1 ) e. ZZ )' % A0)
    z0 = a1(w, A0, '0z', '0 e. ZZ')
    # 1. the index set ( ( J + 1 ) ... ( J + N ) ) = ( ( 0 + K ) ... ( ( N - 1 ) + K ) )
    e1 = w.s([kc], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A0, K, K))
    e2 = w.s([w.s([w.s([nc, one], 'subcld', '( %s -> ( N - 1 ) e. CC )' % A0), kc], 'addcomd', '( %s -> ( ( N - 1 ) + %s ) = ( %s + ( N - 1 ) ) )' % (A0, K, K)),
              w.s([w.s([w.s([jn0], 'nn0cnd', '( %s -> J e. CC )' % A0), one, w.s([nc, one], 'subcld', '( %s -> ( N - 1 ) e. CC )' % A0)], 'addassd',
                       '( %s -> ( ( J + 1 ) + ( N - 1 ) ) = ( J + ( 1 + ( N - 1 ) ) ) )' % A0),
                   w.s([w.s([one, nc], 'pncan3d', '( %s -> ( 1 + ( N - 1 ) ) = N )' % A0)], 'oveq2d', '( %s -> ( J + ( 1 + ( N - 1 ) ) ) = ( J + N ) )' % A0)],
                  'eqtrd', '( %s -> ( ( J + 1 ) + ( N - 1 ) ) = ( J + N ) )' % A0)], 'eqtrd', '( %s -> ( ( N - 1 ) + %s ) = ( J + N ) )' % (A0, K))
    iset = w.s([w.s([e1, e2], 'oveq12d', '( %s -> ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) = ( %s ... ( J + N ) ) )' % (A0, K, K, K))], 'eqcomd',
               '( %s -> ( %s ... ( J + N ) ) = ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) )' % (A0, K, K, K))
    s1 = w.s([iset], 'sumeq1d', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (A0, K, CHV('i'), K, K, CHV('i')))
    # 2. the body as CHV( K + ( i - K ) )
    Ai = '( %s /\\ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) )' % (A0, K, K)
    ic = w.s([w.s([w.s([], 'simpr', '( %s -> i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) )' % (Ai, K, K)), w.inst('elfzelz')], 'syl', '( %s -> i e. ZZ )' % Ai)], 'zcnd',
             '( %s -> i e. CC )' % Ai)
    pc = w.s([w.s([kc], 'adantr', '( %s -> %s e. CC )' % (Ai, K)), ic], 'pncan3d', '( %s -> ( %s + ( i - %s ) ) = i )' % (Ai, K, K))
    s2 = w.s([w.s([w.s([w.s([pc], 'fveq2d', '( %s -> ( %s ` ( %s + ( i - %s ) ) ) = ( %s ` i ) )' % (Ai, LH, K, K, LH))], 'fveq2d',
                        '( %s -> %s = %s )' % (Ai, CHV('( %s + ( i - %s ) )' % (K, K)), CHV('i')))], 'eqcomd', '( %s -> %s = %s )' % (Ai, CHV('i'), CHV('( %s + ( i - %s ) )' % (K, K))))],
             'sumeq2dv', '( %s -> sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (A0, K, K, CHV('i'), K, K, CHV('( %s + ( i - %s ) )' % (K, K))))
    # 3. fsumshft back to ( 0 ... ( N - 1 ) )
    Aj = '( %s /\\ j e. ( 0 ... ( N - 1 ) ) )' % A0
    jn0 = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... ( N - 1 ) ) )' % Aj), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % Aj)
    kjn = w.s([w.s([kn], 'adantr', '( %s -> %s e. NN )' % (Aj, K)), jn0, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( %s + j ) e. NN )' % (Aj, K))
    acl = chvcl(w, Aj, '( %s + j )' % K, w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Aj, DC)), kjn)
    sub = w.s([w.s([w.s([], 'oveq2', '( j = ( i - %s ) -> ( %s + j ) = ( %s + ( i - %s ) ) )' % (K, K, K, K))], 'fveq2d',
                   '( j = ( i - %s ) -> ( %s ` ( %s + j ) ) = ( %s ` ( %s + ( i - %s ) ) ) )' % (K, LH, K, LH, K, K))], 'fveq2d',
              '( j = ( i - %s ) -> %s = %s )' % (K, CHV('( %s + j )' % K), CHV('( %s + ( i - %s ) )' % (K, K))))
    sh = w.s([kz, z0, nm1, acl, sub], 'fsumshft', '( %s -> sum_ j e. ( 0 ... ( N - 1 ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (
        A0, CHV('( %s + j )' % K), K, K, CHV('( %s + ( i - %s ) )' % (K, K))))
    # 4. ( 0 ... ( N - 1 ) ) = W and the body by chrtrl
    fzo = w.s([w.s([d['nz'], w.inst('fzoval')], 'syl', '( %s -> %s = ( 0 ... ( N - 1 ) ) )' % (A0, WIF))], 'eqcomd', '( %s -> ( 0 ... ( N - 1 ) ) = %s )' % (A0, WIF))
    weq = w.s([w.s([w.s([d['nn']], 'nnne0d', '( %s -> N =/= 0 )' % A0), w.inst('ifnefalse')], 'syl', '( %s -> %s = %s )' % (A0, WI, WIF))], 'eqcomd',
              '( %s -> %s = %s )' % (A0, WIF, WI))
    iw = w.s([fzo, weq], 'eqtrd', '( %s -> ( 0 ... ( N - 1 ) ) = %s )' % (A0, WI))
    s4 = w.s([iw], 'sumeq1d', '( %s -> sum_ j e. ( 0 ... ( N - 1 ) ) %s = sum_ j e. %s %s )' % (A0, CHV('( %s + j )' % K), WI, CHV('( %s + j )' % K)))
    Aw = '( %s /\\ j e. %s )' % (A0, WI)
    jw = w.s([], 'simpr', '( %s -> j e. %s )' % (Aw, WI))
    jwf = w.s([jw, w.s([weq], 'adantr', '( %s -> %s = %s )' % (Aw, WIF, WI))], 'eleqtrrd', '( %s -> j e. %s )' % (Aw, WIF))
    jz = w.s([jwf, w.inst('elfzoelz')], 'syl', '( %s -> j e. ZZ )' % Aw)
    C = '( %s ` %s )' % (LH, K)
    trl = w.s([w.s([w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Aw), w.s([kz], 'adantr', '( %s -> %s e. ZZ )' % (Aw, K)), jz], '3jca',
                    '( %s -> ( N e. NN /\\ %s e. ZZ /\\ j e. ZZ ) )' % (Aw, K)), w.inst('chrtrl')], 'syl',
              '( %s -> ( %s ` ( %s + j ) ) = ( %s %s ( %s ` j ) ) )' % (Aw, LH, K, C, PG, LH))
    s5 = w.s([w.s([trl], 'fveq2d', '( %s -> %s = ( X ` ( %s %s ( %s ` j ) ) ) )' % (Aw, CHV('( %s + j )' % K), C, PG, LH))], 'sumeq2dv',
             '( %s -> sum_ j e. %s %s = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, WI, CHV('( %s + j )' % K), WI, C, PG, LH))
    # 5. reindex onto the base along znf1o
    fr = w.s([], 'eqid', '( %s |` %s ) = ( %s |` %s )' % (LH, WI, LH, WI))
    wq = w.s([], 'eqid', '%s = %s' % (WI, WI))
    f1o = w.s([d['nn0'], w.s([d['z'], d['bb'], fr, wq], 'znf1o', '( N e. NN0 -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (LH, WI, WI, BZ))], 'syl',
              '( %s -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (A0, LH, WI, WI, BZ))
    wfin = w.s([w.s([weq], 'eqcomd', '( %s -> %s = %s )' % (A0, WI, WIF)), a1(w, A0, 'fzofi', '%s e. Fin' % WIF)], 'eqeltrd', '( %s -> %s e. Fin )' % (A0, WI))
    fres = w.s([jw, w.inst('fvres')], 'syl', '( %s -> ( ( %s |` %s ) ` j ) = ( %s ` j ) )' % (Aw, LH, WI, LH))
    xf = w.s([d['g'], d['z'], d['b'], d['bb'], d['xd']], 'dchrf', '( %s -> X : %s --> CC )' % (A0, BZ))
    grp = w.s([w.s([w.s([d['nn0'], w.s([d['z']], 'zncrng', '( N e. NN0 -> %s e. CRing )' % ZN)], 'syl', '( %s -> %s e. CRing )' % (A0, ZN)),
                    w.inst('crngring')], 'syl', '( %s -> %s e. Ring )' % (A0, ZN)), w.inst('ringgrp')], 'syl', '( %s -> %s e. Grp )' % (A0, ZN))
    lf = w.s([w.s([d['nn0'], w.s([d['z'], d['bb'], d['l']], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> %s )' % (LH, BZ))], 'syl',
                  '( %s -> %s : ZZ -onto-> %s )' % (A0, LH, BZ)), w.inst('fof')], 'syl', '( %s -> %s : ZZ --> %s )' % (A0, LH, BZ))
    cb = w.s([lf, kz], 'ffvelcdmd', '( %s -> %s e. %s )' % (A0, C, BZ))
    Aa = '( %s /\\ a e. %s )' % (A0, BZ)
    ab = w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, BZ))
    cab = w.s([w.s([grp], 'adantr', '( %s -> %s e. Grp )' % (Aa, ZN)), w.s([cb], 'adantr', '( %s -> %s e. %s )' % (Aa, C, BZ)), ab,
               w.s([d['bb'], w.s([], 'eqid', '%s = %s' % (PG, PG))], 'grpcl', '( ( %s e. Grp /\\ %s e. %s /\\ a e. %s ) -> ( %s %s a ) e. %s )' % (ZN, C, BZ, BZ, C, PG, BZ))],
              'syl3anc', '( %s -> ( %s %s a ) e. %s )' % (Aa, C, PG, BZ))
    xcab = w.s([w.s([xf], 'adantr', '( %s -> X : %s --> CC )' % (Aa, BZ)), cab], 'ffvelcdmd', '( %s -> ( X ` ( %s %s a ) ) e. CC )' % (Aa, C, PG))
    sub5 = w.s([w.s([], 'oveq2', '( a = ( %s ` j ) -> ( %s %s a ) = ( %s %s ( %s ` j ) ) )' % (LH, C, PG, C, PG, LH))], 'fveq2d',
               '( a = ( %s ` j ) -> ( X ` ( %s %s a ) ) = ( X ` ( %s %s ( %s ` j ) ) ) )' % (LH, C, PG, C, PG, LH))
    s6 = w.s([sub5, wfin, f1o, fres, xcab], 'fsumf1o', '( %s -> sum_ a e. %s ( X ` ( %s %s a ) ) = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, BZ, C, PG, WI, C, PG, LH))
    # 6. the translation of the base
    TF = '( t e. %s |-> ( %s %s t ) )' % (BZ, C, PG)
    tf1o = w.s([grp, cb, w.s([d['bb'], w.s([], 'eqid', '%s = %s' % (PG, PG)), w.s([], 'eqid', '%s = %s' % (TF, TF))], 'grplmulf1o',
                              '( ( %s e. Grp /\\ %s e. %s ) -> %s : %s -1-1-onto-> %s )' % (ZN, C, BZ, TF, BZ, BZ))], 'syl2anc',
               '( %s -> %s : %s -1-1-onto-> %s )' % (A0, TF, BZ, BZ))
    bfin = w.s([d['nn'], w.s([d['z'], d['bb']], 'znfi', '( N e. NN -> %s e. Fin )' % BZ)], 'syl', '( %s -> %s e. Fin )' % (A0, BZ))
    tsub = w.s([], 'oveq2', '( t = a -> ( %s %s t ) = ( %s %s a ) )' % (C, PG, C, PG))
    tfv = mpv(w, Aa, TF, 'a', '( %s %s a )' % (C, PG), tsub, ab, vexd(w, Aa, '( %s %s a )' % (C, PG)), BZ)
    Ab = '( %s /\\ b e. %s )' % (A0, BZ)
    xb = w.s([w.s([xf], 'adantr', '( %s -> X : %s --> CC )' % (Ab, BZ)), w.s([], 'simpr', '( %s -> b e. %s )' % (Ab, BZ))], 'ffvelcdmd', '( %s -> ( X ` b ) e. CC )' % Ab)
    sub6 = w.s([], 'fveq2', '( b = ( %s %s a ) -> ( X ` b ) = ( X ` ( %s %s a ) ) )' % (C, PG, C, PG))
    s7 = w.s([sub6, bfin, tf1o, tfv, xb], 'fsumf1o', '( %s -> sum_ b e. %s ( X ` b ) = sum_ a e. %s ( X ` ( %s %s a ) ) )' % (A0, BZ, BZ, C, PG))
    # 7. dchrsum
    o1 = w.s([], 'eqid', '%s = %s' % (ONE, ONE))
    dsum = w.s([d['g'], d['z'], d['b'], o1, d['xd'], d['bb']], 'dchrsum', '( %s -> sum_ b e. %s ( X ` b ) = if ( X = %s , ( phi ` N ) , 0 ) )' % (A0, BZ, ONE))
    # assemble
    c1 = w.s([s1, s2], 'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (A0, K, CHV('i'), K, K, CHV('( %s + ( i - %s ) )' % (K, K))))
    c2 = w.s([c1, w.s([sh], 'eqcomd', '( %s -> sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s = sum_ j e. ( 0 ... ( N - 1 ) ) %s )' % (A0, K, K, CHV('( %s + ( i - %s ) )' % (K, K)), CHV('( %s + j )' % K)))],
             'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ j e. ( 0 ... ( N - 1 ) ) %s )' % (A0, K, CHV('i'), CHV('( %s + j )' % K)))
    c3 = w.s([c2, w.s([s4, s5], 'eqtrd', '( %s -> sum_ j e. ( 0 ... ( N - 1 ) ) %s = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, CHV('( %s + j )' % K), WI, C, PG, LH))],
             'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, K, CHV('i'), WI, C, PG, LH))
    c4 = w.s([c3, w.s([s6], 'eqcomd', '( %s -> sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) = sum_ a e. %s ( X ` ( %s %s a ) ) )' % (A0, WI, C, PG, LH, BZ, C, PG))], 'eqtrd',
             '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ a e. %s ( X ` ( %s %s a ) ) )' % (A0, K, CHV('i'), BZ, C, PG))
    c5 = w.s([c4, w.s([s7], 'eqcomd', '( %s -> sum_ a e. %s ( X ` ( %s %s a ) ) = sum_ b e. %s ( X ` b ) )' % (A0, BZ, C, PG, BZ))], 'eqtrd',
             '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ b e. %s ( X ` b ) )' % (A0, K, CHV('i'), BZ))
    w.qed([c5, dsum], 'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = if ( X = %s , ( phi ` N ) , 0 ) )' % (A0, K, CHV('i'), ONE))
    go(w)



# ---------------------------------------------------------------- zl1wblk
PHN = '( ( phi ` N ) / N )'
IFP = 'if ( X = %s , ( phi ` N ) , 0 )' % ONE
if not only or 'zl1wblk' in only:
    w = W('zl1wblk', 'The mean-free values ` X ( i ) - q ` of a Dirichlet character sum to zero over any block of ` N ` '
          'consecutive positive integers ( ~ zl1blk ; ` N q = if ( X = 1 , phi ( N ) , 0 ) ` ).')
    A0 = '( %s /\\ J e. NN0 )' % NX
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    d = nxctx(w, A0, nx)
    jn0 = w.s([], 'simpr', '( %s -> J e. NN0 )' % A0)
    KS = '( ( J + 1 ) ... ( J + N ) )'
    Ai = '( %s /\\ i e. %s )' % (A0, KS)
    iz = w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, KS)), w.inst('elfzelz')], 'syl', '( %s -> i e. ZZ )' % Ai)
    j1 = w.s([w.s([w.s([jn0], 'adantr', '( %s -> J e. NN0 )' % Ai), w.inst('nn0p1nn')], 'syl', '( %s -> ( J + 1 ) e. NN )' % Ai)], 'nnge1d', '( %s -> 1 <_ ( J + 1 ) )' % Ai)
    j1i = w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, KS)), w.inst('elfzle1')], 'syl', '( %s -> ( J + 1 ) <_ i )' % Ai)
    i1 = w.s([a1(w, Ai, '1re', '1 e. RR'), w.s([w.s([w.s([jn0], 'adantr', '( %s -> J e. NN0 )' % Ai), w.inst('nn0p1nn')], 'syl', '( %s -> ( J + 1 ) e. NN )' % Ai)], 'nnred',
                                             '( %s -> ( J + 1 ) e. RR )' % Ai), w.s([iz], 'zred', '( %s -> i e. RR )' % Ai), j1, j1i], 'letrd', '( %s -> 1 <_ i )' % Ai)
    inn = w.s([w.s([iz, i1], 'jca', '( %s -> ( i e. ZZ /\\ 1 <_ i ) )' % Ai), w.inst('elnnz1')], 'sylibr', '( %s -> i e. NN )' % Ai)
    nxi = w.s([nx], 'adantr', '( %s -> %s )' % (Ai, NX))
    nni = w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Ai)
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, KS))
    qc = qmcl(w, A0, d['nn'])
    fs = w.s([fin, chvcl(w, Ai, 'i', nxi, inn), qmcl(w, Ai, nni)], 'fsumsub', '( %s -> sum_ i e. %s %s = ( sum_ i e. %s %s - sum_ i e. %s %s ) )' % (A0, KS, CHW('i'), KS, CHV('i'), KS, QM))
    bl = w.s([w.s([nx, jn0], 'jca', '( %s -> ( %s /\\ J e. NN0 ) )' % (A0, NX)), w.inst('zl1blk')], 'syl', '( %s -> sum_ i e. %s %s = %s )' % (A0, KS, CHV('i'), IFP))
    cst = w.s([fin, qc, w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ i e. %s %s = ( ( # ` %s ) x. %s ) )' % (A0, KS, QM, KS, QM))
    jz = w.s([jn0], 'nn0zd', '( %s -> J e. ZZ )' % A0)
    jr = w.s([jn0], 'nn0red', '( %s -> J e. RR )' % A0)
    j1z = w.s([jz, a1(w, A0, '1z', '1 e. ZZ')], 'zaddcld', '( %s -> ( J + 1 ) e. ZZ )' % A0)
    jnz = w.s([jz, d['nz']], 'zaddcld', '( %s -> ( J + N ) e. ZZ )' % A0)
    le = w.s([a1(w, A0, '1re', '1 e. RR'), w.s([d['nn']], 'nnred', '( %s -> N e. RR )' % A0), jr, w.s([d['nn']], 'nnge1d', '( %s -> 1 <_ N )' % A0)], 'leadd2dd', '( %s -> ( J + 1 ) <_ ( J + N ) )' % A0)
    uz = w.s([w.s([j1z, jnz, le], '3jca', '( %s -> ( ( J + 1 ) e. ZZ /\\ ( J + N ) e. ZZ /\\ ( J + 1 ) <_ ( J + N ) ) )' % A0),
              w.s([], 'eluz2', '( ( J + N ) e. ( ZZ>= ` ( J + 1 ) ) <-> ( ( J + 1 ) e. ZZ /\\ ( J + N ) e. ZZ /\\ ( J + 1 ) <_ ( J + N ) ) )')], 'sylibr',
             '( %s -> ( J + N ) e. ( ZZ>= ` ( J + 1 ) ) )' % A0)
    hs = w.s([uz, w.inst('hashfz')], 'syl', '( %s -> ( # ` %s ) = ( ( ( J + N ) - ( J + 1 ) ) + 1 ) )' % (A0, KS))
    jc = w.s([jn0], 'nn0cnd', '( %s -> J e. CC )' % A0); nc = w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % A0); oc = a1(w, A0, 'ax-1cn', '1 e. CC')
    hs2 = chain(w, A0, ['( # ` %s )' % KS, '( ( ( J + N ) - ( J + 1 ) ) + 1 )', '( ( N - 1 ) + 1 )', 'N'],
                [hs, E(w, A0, 'oveq1d', [E(w, A0, 'pnpcand', [jc, nc, oc], '( ( J + N ) - ( J + 1 ) )', '( N - 1 )')], '( ( ( J + N ) - ( J + 1 ) ) + 1 )', '( ( N - 1 ) + 1 )'),
                 E(w, A0, 'npcand', [nc, oc], '( ( N - 1 ) + 1 )', 'N')])
    pc = w.s([w.s([w.s([d['nn'], w.inst('phicl')], 'syl', '( %s -> ( phi ` N ) e. NN )' % A0)], 'nncnd', '( %s -> ( phi ` N ) e. CC )' % A0)], 'idi', '( %s -> ( phi ` N ) e. CC )' % A0)
    nq = chain(w, A0, ['( N x. %s )' % QM, 'if ( X = %s , ( N x. %s ) , ( N x. 0 ) )' % (ONE, PHN), IFP],
               [w.s([w.s([], 'ovif2', '( N x. %s ) = if ( X = %s , ( N x. %s ) , ( N x. 0 ) )' % (QM, ONE, PHN))], 'a1i', '( %s -> ( N x. %s ) = if ( X = %s , ( N x. %s ) , ( N x. 0 ) ) )' % (A0, QM, ONE, PHN)),
                w.s([E(w, A0, 'divcan2d', [pc, nc, w.s([d['nn']], 'nnne0d', '( %s -> N =/= 0 )' % A0)], '( N x. %s )' % PHN, '( phi ` N )'),
                     E(w, A0, 'mul01d', [nc], '( N x. 0 )', '0')], 'ifeq12d', '( %s -> if ( X = %s , ( N x. %s ) , ( N x. 0 ) ) = %s )' % (A0, ONE, PHN, IFP))])
    cs2 = chain(w, A0, ['sum_ i e. %s %s' % (KS, QM), '( ( # ` %s ) x. %s )' % (KS, QM), '( N x. %s )' % QM, IFP],
                [cst, E(w, A0, 'oveq1d', [hs2], '( ( # ` %s ) x. %s )' % (KS, QM), '( N x. %s )' % QM), nq])
    ifc = w.s([pc, a1(w, A0, '0cn', '0 e. CC')], 'ifcld', '( %s -> %s e. CC )' % (A0, IFP))
    chain(w, A0, ['sum_ i e. %s %s' % (KS, CHW('i')), '( sum_ i e. %s %s - sum_ i e. %s %s )' % (KS, CHV('i'), KS, QM), '( %s - %s )' % (IFP, IFP), '0'],
          [fs, E(w, A0, 'oveq12d', [bl, cs2], '( sum_ i e. %s %s - sum_ i e. %s %s )' % (KS, CHV('i'), KS, QM), '( %s - %s )' % (IFP, IFP)),
           E(w, A0, 'subidd', [ifc], '( %s - %s )' % (IFP, IFP), '0')], name='qed')
    go(w)

# ---------------------------------------------------------------- zl1wper
if not only or 'zl1wper' in only:
    w = W('zl1wper', 'The partial sums of the mean-free values ` X ( i ) - q ` of a Dirichlet character are periodic '
          'with period ` N ` ( ~ zl1wblk ; C5\'s ~ chrsper ).')
    A0 = '( %s /\\ J e. NN0 )' % NX
    d = nxctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, NX)))
    jn0 = w.s([], 'simpr', '( %s -> J e. NN0 )' % A0)
    jr = w.s([jn0], 'nn0red', '( %s -> J e. RR )' % A0)
    jz = w.s([jn0], 'nn0zd', '( %s -> J e. ZZ )' % A0)
    A_ = '( 1 ... J )'; B_ = '( ( J + 1 ) ... ( J + N ) )'; U_ = '( 1 ... ( J + N ) )'
    dis = w.s([w.s([jr], 'ltp1d', '( %s -> J < ( J + 1 ) )' % A0), w.inst('fzdisj')], 'syl', '( %s -> ( %s i^i %s ) = (/) )' % (A0, A_, B_))
    j1u = w.s([w.s([jn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( J + 1 ) e. NN )' % A0), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> ( J + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
    jnz = w.s([jz, d['nz']], 'zaddcld', '( %s -> ( J + N ) e. ZZ )' % A0)
    jle = w.s([jr, d['nn0'], w.inst('nn0addge1')], 'syl2anc', '( %s -> J <_ ( J + N ) )' % A0)
    jnu = w.s([w.s([jz, jnz, jle], '3jca', '( %s -> ( J e. ZZ /\\ ( J + N ) e. ZZ /\\ J <_ ( J + N ) ) )' % A0),
               w.s([], 'eluz2', '( ( J + N ) e. ( ZZ>= ` J ) <-> ( J e. ZZ /\\ ( J + N ) e. ZZ /\\ J <_ ( J + N ) ) )')], 'sylibr', '( %s -> ( J + N ) e. ( ZZ>= ` J ) )' % A0)
    spl = w.s([j1u, jnu, w.inst('fzsplit2')], 'syl2anc', '( %s -> %s = ( %s u. %s ) )' % (A0, U_, A_, B_))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, U_))
    Ai = '( %s /\\ i e. %s )' % (A0, U_)
    icl = chwcl(w, Ai, 'i', w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ai, DC)),
                w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, U_)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai), w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Ai))
    sp = w.s([dis, spl, fin, icl], 'fsumsplit', '( %s -> %s = ( %s + sum_ i e. %s %s ) )' % (A0, PSW('( J + N )'), PSW('J'), B_, CHW('i')))
    blk = w.s([], 'zl1wblk', '( %s -> sum_ i e. %s %s = 0 )' % (A0, B_, CHW('i')))
    Aj = '( %s /\\ i e. %s )' % (A0, A_)
    jcl = chwcl(w, Aj, 'i', w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Aj, DC)),
                w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Aj, A_)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Aj), w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Aj))
    scl = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, A_)), jcl], 'fsumcl', '( %s -> %s e. CC )' % (A0, PSW('J')))
    w.qed([sp, w.s([w.s([blk], 'oveq2d', '( %s -> ( %s + sum_ i e. %s %s ) = ( %s + 0 ) )' % (A0, PSW('J'), B_, CHW('i'), PSW('J'))),
                    w.s([scl], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A0, PSW('J'), PSW('J')))], 'eqtrd',
                   '( %s -> ( %s + sum_ i e. %s %s ) = %s )' % (A0, PSW('J'), B_, CHW('i'), PSW('J')))], 'eqtrd',
          '( %s -> %s = %s )' % (A0, PSW('( J + N )'), PSW('J')))
    go(w)



# ---------------------------------------------------------------- zl1wmod
if not only or 'zl1wmod' in only:
    w = W('zl1wmod', 'The partial sums of the mean-free values of a Dirichlet character depend only on the index modulo ` N ` '
          '( ~ nn0ind on the number of periods; C5\'s ~ chrsmod ).')
    C0 = '( %s /\\ P e. NN0 )' % NX
    S0 = PSW('P')


    def PH(x):
        return '( %s -> %s = %s )' % (C0, PSW('( P + ( N x. %s ) )' % x), S0)


    def SUBH(x, t):
        """( x = t -> ( PH(x) <-> PH(t) ) )"""
        s = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( N x. %s ) = ( N x. %s ) )' % (x, t, x, t))], 'oveq2d',
                           '( %s = %s -> ( P + ( N x. %s ) ) = ( P + ( N x. %s ) ) )' % (x, t, x, t))], 'oveq2d',
                      '( %s = %s -> ( 1 ... ( P + ( N x. %s ) ) ) = ( 1 ... ( P + ( N x. %s ) ) ) )' % (x, t, x, t))], 'sumeq1d',
                 '( %s = %s -> %s = %s )' % (x, t, PSW('( P + ( N x. %s ) )' % x), PSW('( P + ( N x. %s ) )' % t)))
        e = w.s([s], 'eqeq1d', '( %s = %s -> ( %s = %s <-> %s = %s ) )' % (x, t, PSW('( P + ( N x. %s ) )' % x), S0, PSW('( P + ( N x. %s ) )' % t), S0))
        return w.s([e], 'imbi2d', '( %s = %s -> ( %s <-> %s ) )' % (x, t, PH(x), PH(t)))


    h1 = SUBH('x', '0'); h2 = SUBH('x', 'y'); h3 = SUBH('x', '( y + 1 )'); h4 = SUBH('x', 'Q')
    # base
    d = nxctx(w, C0, w.s([], 'simpl', '( %s -> %s )' % (C0, NX)))
    pn0 = w.s([], 'simpr', '( %s -> P e. NN0 )' % C0)
    pc = w.s([pn0], 'nn0cnd', '( %s -> P e. CC )' % C0)
    nc = w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % C0)
    b1 = w.s([w.s([w.s([nc], 'mul01d', '( %s -> ( N x. 0 ) = 0 )' % C0)], 'oveq2d', '( %s -> ( P + ( N x. 0 ) ) = ( P + 0 ) )' % C0),
              w.s([pc], 'addridd', '( %s -> ( P + 0 ) = P )' % C0)], 'eqtrd', '( %s -> ( P + ( N x. 0 ) ) = P )' % C0)
    base = w.s([w.s([b1], 'oveq2d', '( %s -> ( 1 ... ( P + ( N x. 0 ) ) ) = ( 1 ... P ) )' % C0)], 'sumeq1d', PH('0'))
    # step
    Ay = '( y e. NN0 /\\ %s )' % C0
    yn0 = w.s([], 'simpl', '( %s -> y e. NN0 )' % Ay)
    c0 = w.s([], 'simpr', '( %s -> %s )' % (Ay, C0))
    dy = nxctx(w, Ay, w.s([c0, w.inst('simpl')], 'syl', '( %s -> %s )' % (Ay, NX)))
    pn0y = w.s([c0, w.inst('simpr')], 'syl', '( %s -> P e. NN0 )' % Ay)
    ncy = w.s([dy['nn']], 'nncnd', '( %s -> N e. CC )' % Ay)
    yc = w.s([yn0], 'nn0cnd', '( %s -> y e. CC )' % Ay)
    pcy = w.s([pn0y], 'nn0cnd', '( %s -> P e. CC )' % Ay)
    J_ = '( P + ( N x. y ) )'
    e1 = w.s([w.s([ncy, yc, a1(w, Ay, 'ax-1cn', '1 e. CC')], 'adddid', '( %s -> ( N x. ( y + 1 ) ) = ( ( N x. y ) + ( N x. 1 ) ) )' % Ay),
              w.s([w.s([ncy], 'mulridd', '( %s -> ( N x. 1 ) = N )' % Ay)], 'oveq2d', '( %s -> ( ( N x. y ) + ( N x. 1 ) ) = ( ( N x. y ) + N ) )' % Ay)], 'eqtrd',
             '( %s -> ( N x. ( y + 1 ) ) = ( ( N x. y ) + N ) )' % Ay)
    e2 = w.s([w.s([e1], 'oveq2d', '( %s -> ( P + ( N x. ( y + 1 ) ) ) = ( P + ( ( N x. y ) + N ) ) )' % Ay),
              w.s([w.s([pcy, w.s([ncy, yc], 'mulcld', '( %s -> ( N x. y ) e. CC )' % Ay), ncy], 'addassd', '( %s -> ( ( P + ( N x. y ) ) + N ) = ( P + ( ( N x. y ) + N ) ) )' % Ay)],
                  'eqcomd', '( %s -> ( P + ( ( N x. y ) + N ) ) = ( %s + N ) )' % (Ay, J_))], 'eqtrd', '( %s -> ( P + ( N x. ( y + 1 ) ) ) = ( %s + N ) )' % (Ay, J_))
    s1 = w.s([w.s([e2], 'oveq2d', '( %s -> ( 1 ... ( P + ( N x. ( y + 1 ) ) ) ) = ( 1 ... ( %s + N ) ) )' % (Ay, J_))], 'sumeq1d',
             '( %s -> %s = %s )' % (Ay, PSW('( P + ( N x. ( y + 1 ) ) )'), PSW('( %s + N )' % J_)))
    jn0 = w.s([pn0y, w.s([dy['nn0'], yn0], 'nn0mulcld', '( %s -> ( N x. y ) e. NN0 )' % Ay)], 'nn0addcld', '( %s -> %s e. NN0 )' % (Ay, J_))
    per = w.s([w.s([dy['nx'], jn0], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (Ay, NX, J_)), w.inst('zl1wper')], 'syl',
              '( %s -> %s = %s )' % (Ay, PSW('( %s + N )' % J_), PSW(J_)))
    s12 = w.s([s1, per], 'eqtrd', '( %s -> %s = %s )' % (Ay, PSW('( P + ( N x. ( y + 1 ) ) )'), PSW(J_)))
    Ayh = '( %s /\\ %s = %s )' % (Ay, PSW(J_), S0)
    st = w.s([w.s([s12], 'adantr', '( %s -> %s = %s )' % (Ayh, PSW('( P + ( N x. ( y + 1 ) ) )'), PSW(J_))),
              w.s([], 'simpr', '( %s -> %s = %s )' % (Ayh, PSW(J_), S0))], 'eqtrd', '( %s -> %s = %s )' % (Ayh, PSW('( P + ( N x. ( y + 1 ) ) )'), S0))
    st1 = w.s([st], 'ex', '( %s -> ( %s = %s -> %s = %s ) )' % (Ay, PSW(J_), S0, PSW('( P + ( N x. ( y + 1 ) ) )'), S0))
    st2 = w.s([st1], 'ex', '( y e. NN0 -> ( %s -> ( %s = %s -> %s = %s ) ) )' % (C0, PSW(J_), S0, PSW('( P + ( N x. ( y + 1 ) ) )'), S0))
    step = w.s([st2], 'a2d', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH('( y + 1 )')))
    ind = w.s([h1, h2, h3, h4, base, step], 'nn0ind', '( Q e. NN0 -> %s )' % PH('Q'))
    w.qed([w.s([w.s([ind], 'com12', '( %s -> ( Q e. NN0 -> %s = %s ) )' % (C0, PSW('( P + ( N x. Q ) )'), S0))], 'imp',
               '( ( %s /\\ Q e. NN0 ) -> %s = %s )' % (C0, PSW('( P + ( N x. Q ) )'), S0))], 'anasss',
          '( ( %s /\\ ( P e. NN0 /\\ Q e. NN0 ) ) -> %s = %s )' % (NX, PSW('( P + ( N x. Q ) )'), S0))
    go(w)



# ---------------------------------------------------------------- zl1wbnd
if not only or 'zl1wbnd' in only:
    w = W('zl1wbnd', 'The partial sums of the mean-free values ` X ( i ) - q ` of a Dirichlet character are bounded by '
          '` N ( 1 + | q | ) ` ( ~ zl1wmod ; as C5 ~ chrsbnd ).')
    A0 = '( %s /\\ M e. NN0 )' % NX
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    d = nxctx(w, A0, nx)
    mn0 = w.s([], 'simpr', '( %s -> M e. NN0 )' % A0)
    mr = w.s([mn0], 'nn0red', '( %s -> M e. RR )' % A0)
    mz = w.s([mn0], 'nn0zd', '( %s -> M e. ZZ )' % A0)
    nrp = w.s([d['nn']], 'nnrpd', '( %s -> N e. RR+ )' % A0)
    nr = w.s([d['nn']], 'nnred', '( %s -> N e. RR )' % A0)
    R_ = '( M mod N )'; Q_ = '( |_ ` ( M / N ) )'
    mv = w.s([mr, nrp, w.inst('modval')], 'syl2anc', '( %s -> %s = ( M - ( N x. %s ) ) )' % (A0, R_, Q_))
    rn0 = w.s([mz, d['nn'], w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, R_))
    mdn = w.s([mr, nrp], 'rerpdivcld', '( %s -> ( M / N ) e. RR )' % A0)
    mdg = w.s([w.s([mr, w.s([mn0], 'nn0ge0d', '( %s -> 0 <_ M )' % A0)], 'jca', '( %s -> ( M e. RR /\\ 0 <_ M ) )' % A0),
               w.s([nr, w.s([d['nn']], 'nngt0d', '( %s -> 0 < N )' % A0)], 'jca', '( %s -> ( N e. RR /\\ 0 < N ) )' % A0), w.inst('divge0')], 'syl2anc', '( %s -> 0 <_ ( M / N ) )' % A0)
    qn0 = w.s([mdn, mdg, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, Q_))
    nq = w.s([w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % A0), w.s([qn0], 'nn0cnd', '( %s -> %s e. CC )' % (A0, Q_))], 'mulcld', '( %s -> ( N x. %s ) e. CC )' % (A0, Q_))
    idm = w.s([w.s([mv], 'oveq1d', '( %s -> ( %s + ( N x. %s ) ) = ( ( M - ( N x. %s ) ) + ( N x. %s ) ) )' % (A0, R_, Q_, Q_, Q_)),
               w.s([w.s([mn0], 'nn0cnd', '( %s -> M e. CC )' % A0), nq], 'npcand', '( %s -> ( ( M - ( N x. %s ) ) + ( N x. %s ) ) = M )' % (A0, Q_, Q_))], 'eqtrd',
              '( %s -> ( %s + ( N x. %s ) ) = M )' % (A0, R_, Q_))
    md = w.s([w.s([nx, w.s([rn0, qn0], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (A0, R_, Q_))], 'jca', '( %s -> ( %s /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) )' % (A0, NX, R_, Q_)),
              w.inst('zl1wmod')], 'syl', '( %s -> %s = %s )' % (A0, PSW('( %s + ( N x. %s ) )' % (R_, Q_)), PSW(R_)))
    eqm = w.s([w.s([w.s([w.s([idm], 'oveq2d', '( %s -> ( 1 ... ( %s + ( N x. %s ) ) ) = ( 1 ... M ) )' % (A0, R_, Q_))], 'sumeq1d',
                        '( %s -> %s = %s )' % (A0, PSW('( %s + ( N x. %s ) )' % (R_, Q_)), PSW('M')))], 'eqcomd', '( %s -> %s = %s )' % (A0, PSW('M'), PSW('( %s + ( N x. %s ) )' % (R_, Q_)))), md],
              'eqtrd', '( %s -> %s = %s )' % (A0, PSW('M'), PSW(R_)))
    Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (A0, R_)
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, R_)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
    nxi = w.s([nx], 'adantr', '( %s -> %s )' % (Ai, NX))
    nni = w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Ai)
    icl = chwcl(w, Ai, 'i', nxi, inn, nni)
    CB1 = '( 1 + ( abs ` %s ) )' % QM
    qci = qmcl(w, Ai, nni)
    t1 = w.s([chvcl(w, Ai, 'i', nxi, inn), qci, w.inst('abs2dif2')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (Ai, CHW('i'), CHV('i'), QM))
    t2 = w.s([w.s([chvcl(w, Ai, 'i', nxi, inn)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHV('i'))), a1(w, Ai, '1re', '1 e. RR'), w.s([qci], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, QM)),
              w.s([w.s([nxi, inn], 'jca', '( %s -> ( %s /\\ i e. NN ) )' % (Ai, NX)), w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (Ai, CHV('i')))], 'leadd1dd',
             '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ %s )' % (Ai, CHV('i'), QM, CB1))
    cbr = w.s([a1(w, A0, '1re', '1 e. RR'), w.s([qmcl(w, A0, d['nn'])], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, QM))], 'readdcld', '( %s -> %s e. RR )' % (A0, CB1))
    cbri = w.s([cbr], 'adantr', '( %s -> %s e. RR )' % (Ai, CB1))
    iab = w.s([w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHW('i'))), w.s([w.s([chvcl(w, Ai, 'i', nxi, inn)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHV('i'))),
                                                                                      w.s([qci], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, QM))], 'readdcld',
                                                                                     '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (Ai, CHV('i'), QM)), cbri, t1, t2], 'letrd',
              '( %s -> ( abs ` %s ) <_ %s )' % (Ai, CHW('i'), CB1))
    fin = w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (A0, R_))
    ab1 = w.s([fin, icl], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ i e. ( 1 ... %s ) ( abs ` %s ) )' % (A0, PSW(R_), R_, CHW('i')))
    le1 = w.s([fin, w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHW('i'))), cbri, iab], 'fsumle',
              '( %s -> sum_ i e. ( 1 ... %s ) ( abs ` %s ) <_ sum_ i e. ( 1 ... %s ) %s )' % (A0, R_, CHW('i'), R_, CB1))
    cst = w.s([fin, w.s([cbr], 'recnd', '( %s -> %s e. CC )' % (A0, CB1)), w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ i e. ( 1 ... %s ) %s = ( ( # ` ( 1 ... %s ) ) x. %s ) )' % (A0, R_, CB1, R_, CB1))
    hs = w.s([rn0, w.inst('hashfz1')], 'syl', '( %s -> ( # ` ( 1 ... %s ) ) = %s )' % (A0, R_, R_))
    cst2 = w.s([cst, w.s([hs], 'oveq1d', '( %s -> ( ( # ` ( 1 ... %s ) ) x. %s ) = ( %s x. %s ) )' % (A0, R_, CB1, R_, CB1))], 'eqtrd',
               '( %s -> sum_ i e. ( 1 ... %s ) %s = ( %s x. %s ) )' % (A0, R_, CB1, R_, CB1))
    rr = w.s([rn0], 'nn0red', '( %s -> %s e. RR )' % (A0, R_))
    rle = w.s([rr, nr, w.s([mr, nrp, w.inst('modlt')], 'syl2anc', '( %s -> %s < N )' % (A0, R_))], 'ltled', '( %s -> %s <_ N )' % (A0, R_))
    qa0 = w.s([qmcl(w, A0, d['nn'])], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, QM))
    cb0 = w.s([a1(w, A0, '1re', '1 e. RR'), w.s([qmcl(w, A0, d['nn'])], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, QM)), a1(w, A0, '0le1', '0 <_ 1'), qa0], 'addge0d',
              '( %s -> 0 <_ %s )' % (A0, CB1))
    rn = w.s([rr, nr, cbr, cb0, rle], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( N x. %s ) )' % (A0, R_, CB1, CB1))
    scl = w.s([fin, icl], 'fsumcl', '( %s -> %s e. CC )' % (A0, PSW(R_)))
    abr = w.s([scl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, PSW(R_)))
    sar = w.s([fin, w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHW('i')))], 'fsumrecl', '( %s -> sum_ i e. ( 1 ... %s ) ( abs ` %s ) e. RR )' % (A0, R_, CHW('i')))
    rcb = w.s([rr, cbr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, R_, CB1))
    le2 = w.s([le1, cst2], 'breqtrd', '( %s -> sum_ i e. ( 1 ... %s ) ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, R_, CHW('i'), R_, CB1))
    t3 = w.s([abr, sar, rcb, ab1, le2], 'letrd', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, PSW(R_), R_, CB1))
    t4 = w.s([abr, rcb, w.s([nr, cbr], 'remulcld', '( %s -> %s e. RR )' % (A0, BW)), t3, rn], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, PSW(R_), BW))
    w.qed([w.s([eqm], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, PSW('M'), PSW(R_))), t4], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, PSW('M'), BW))
    go(w)


def chwabs(w, Ai, i, nxi, inn, nni):
    """( Ai -> ( abs ` CHW(i) ) <_ ( 1 + ( abs ` QM ) ) )"""
    CB1 = '( 1 + ( abs ` %s ) )' % QM
    qci = qmcl(w, Ai, nni)
    cv = chvcl(w, Ai, i, nxi, inn)
    t1 = w.s([cv, qci, w.inst('abs2dif2')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (Ai, CHW(i), CHV(i), QM))
    t2 = w.s([w.s([cv], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHV(i))), a1(w, Ai, '1re', '1 e. RR'), w.s([qci], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, QM)),
              w.s([w.s([nxi, inn], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (Ai, NX, i)), w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (Ai, CHV(i)))], 'leadd1dd',
             '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ %s )' % (Ai, CHV(i), QM, CB1))
    cbr = w.s([a1(w, Ai, '1re', '1 e. RR'), w.s([qci], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, QM))], 'readdcld', '( %s -> %s e. RR )' % (Ai, CB1))
    return w.s([w.s([chwcl(w, Ai, i, nxi, inn, nni)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHW(i))),
                w.s([w.s([cv], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHV(i))), w.s([qci], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, QM))], 'readdcld',
                    '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (Ai, CHV(i), QM)), cbr, t1, t2], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (Ai, CHW(i), CB1))


# ---------------------------------------------------------------- zl1wcsf
if not only or 'zl1wcsf' in only:
    w = W('zl1wcsf', 'The partial sums of the mean-free values of a Dirichlet character, as a bounded sequence in C4\'s '
          'partial-sum interface ( ~ abbnd ), with the bound ` N ( 1 + | q | ) ` ( ~ zl1wbnd ).')
    A0 = NX
    nx = w.s([], 'id', '( %s -> %s )' % (A0, NX))
    d = nxctx(w, A0, nx)
    Aq = '( %s /\\ q e. NN )' % A0
    Aqi = '( %s /\\ i e. ( 1 ... q ) )' % Aq
    icl = chwcl(w, Aqi, 'i', w.s([nx], 'ad2antrr', '( %s -> %s )' % (Aqi, NX)), w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... q ) )' % Aqi), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Aqi),
                w.s([d['nn']], 'ad2antrr', '( %s -> N e. NN )' % Aqi))
    scl = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... q ) e. Fin )' % Aq), icl], 'fsumcl', '( %s -> %s e. CC )' % (Aq, PSW('q')))
    cf = w.s([scl, w.s([], 'eqid', '%s = %s' % (WSF, WSF))], 'fmptd', '( %s -> %s : NN --> CC )' % (A0, WSF))
    br = w.s([w.s([d['nn']], 'nnred', '( %s -> N e. RR )' % A0), w.s([a1(w, A0, '1re', '1 e. RR'), w.s([qmcl(w, A0, d['nn'])], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, QM))],
                                                                 'readdcld', '( %s -> ( 1 + ( abs ` %s ) ) e. RR )' % (A0, QM))], 'remulcld', '( %s -> %s e. RR )' % (A0, BW))
    Am = '( %s /\\ m e. NN )' % A0
    mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
    val, _ = mptval(w, Am, 'q', 'NN', PSW('q'), 'm', mn, mp=WSF, exs=vexd(w, Am, PSW('m'), 'sum'))
    bd = w.s([w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Am, NX)), w.s([mn], 'nnnn0d', '( %s -> m e. NN0 )' % Am)], 'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (Am, NX)), w.inst('zl1wbnd')], 'syl',
             '( %s -> ( abs ` %s ) <_ %s )' % (Am, PSW('m'), BW))
    bd2 = w.s([w.s([val], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (Am, WSF, PSW('m'))), bd], 'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ %s )' % (Am, WSF, BW))
    w.qed([cf, br, w.s([bd2], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (A0, WSF, BW))], '3jca',
          '( %s -> ( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) )' % (A0, WSF, BW, WSF, BW))
    go(w)

ASW = lambda z, D=HPZ: '( %s e. %s |-> sum_ k e. NN ( ( %s ` k ) x. %s ) )' % (z, D, WSF, DLT('k', z))
CSFP = '( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (WSF, BW, WSF, BW)


def absum(w, ante, Z):
    """( ante -> sum_ k ( ( WSF ` k ) x. DLT ) = AB ( Z ) ) for ante without k"""
    Ak = '( %s /\\ k e. NN )' % ante
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    cv, _ = mptval(w, Ak, 'q', 'NN', PSW('q'), 'k', kn, mp=WSF, exs=vexd(w, Ak, PSW('k'), 'sum'))
    return w.s([w.s([cv], 'oveq1d', '( %s -> ( ( %s ` k ) x. %s ) = ( %s x. %s ) )' % (Ak, WSF, DLT('k', Z), PSW('k'), DLT('k', Z)))], 'sumeq2dv',
               '( %s -> sum_ k e. NN ( ( %s ` k ) x. %s ) = %s )' % (ante, WSF, DLT('k', Z), AB(Z)))


# ---------------------------------------------------------------- zl1ahol
if not only or 'zl1ahol' in only:
    w = W('zl1ahol', 'The Abel series of the mean-free values of a Dirichlet character is holomorphic on the open right '
          'half-plane ( ~ abhol at ~ zl1wcsf ; C5\'s ~ lchrhol0 for every character).')
    A0 = NX
    csf = w.s([], 'zl1wcsf', '( %s -> %s )' % (A0, CSFP))
    hol = w.s([w.s([csf, w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '0le0', '0 <_ 0')], 'jca', '( %s -> ( 0 e. RR /\\ 0 <_ 0 ) )' % A0)], 'jca',
                   '( %s -> ( %s /\\ ( 0 e. RR /\\ 0 <_ 0 ) ) )' % (A0, CSFP)), w.inst('abhol')], 'syl', '( %s -> %s )' % (A0, HOL(ASW('z'), HPZ)))
    Az = '( %s /\\ z e. %s )' % (A0, HPZ)
    eq = w.s([absum(w, Az, 'z')], 'mpteq2dva', '( %s -> %s = %s )' % (A0, ASW('z'), ABF()))
    b1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A0, ASW('z'), HPZ, ABF(), HPZ))
    b2 = w.s([w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, ASW('z'), ABF()))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, ASW('z'), ABF()))],
             'sseq2d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A0, HPZ, ASW('z'), HPZ, ABF()))
    w.qed([hol, w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A0, HOL(ASW('z'), HPZ), HOL(ABF(), HPZ)))], 'mpbid', '( %s -> %s )' % (A0, HOL(ABF(), HPZ)))
    go(w)

# ---------------------------------------------------------------- zl1acl
if not only or 'zl1acl' in only:
    w = W('zl1acl', 'The Abel series of the mean-free values of a Dirichlet character converges on the open right half-plane ( ~ abcl ).')
    A0 = '( %s /\\ ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % NX
    csf = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, NX)), w.inst('zl1wcsf')], 'syl', '( %s -> %s )' % (A0, CSFP))
    c = w.s([w.s([csf, w.s([], 'simpr', '( %s -> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( Z e. CC /\\ 0 < ( Re ` Z ) ) ) )' % (A0, CSFP)), w.inst('abcl')],
            'syl', '( %s -> sum_ k e. NN ( ( %s ` k ) x. %s ) e. CC )' % (A0, WSF, DLT('k', 'Z')))
    w.qed([absum(w, A0, 'Z'), c], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, AB('Z')))
    go(w)

# ---------------------------------------------------------------- zl1aagr
AW = '( q e. NN |-> %s )' % CHW('q')
CB1 = '( 1 + ( abs ` %s ) )' % QM
if not only or 'zl1aagr' in only:
    w = W('zl1aagr', 'The Abel series of the mean-free values of a Dirichlet character agrees with their L-series to the '
          'right of the line one ( ~ abagr ; C5\'s ~ lchragr for every character).')
    ZP1 = '( Z e. CC /\\ 1 < ( Re ` Z ) )'
    A0 = '( %s /\\ %s )' % (NX, ZP1)
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    zp = w.s([], 'simpr', '( %s -> %s )' % (A0, ZP1))
    d = nxctx(w, A0, nx)
    Am = '( %s /\\ m e. NN )' % A0
    mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
    nxm = w.s([nx], 'adantr', '( %s -> %s )' % (Am, NX)); nnm = w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Am)
    awm, _ = mptval(w, Am, 'q', 'NN', CHW('q'), 'm', mn, mp=AW)
    awf = w.s([awm, chwcl(w, Am, 'm', nxm, mn, nnm)], 'eqeltrd', '( %s -> ( %s ` m ) e. CC )' % (Am, AW))
    Aq = '( %s /\\ q e. NN )' % A0
    fq = w.s([chwcl(w, Aq, 'q', w.s([nx], 'adantr', '( %s -> %s )' % (Aq, NX)), w.s([], 'simpr', '( %s -> q e. NN )' % Aq), w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Aq)),
              w.s([], 'eqid', '%s = %s' % (AW, AW))], 'fmptd', '( %s -> %s : NN --> CC )' % (A0, AW))
    cbr = w.s([a1(w, A0, '1re', '1 e. RR'), w.s([qmcl(w, A0, d['nn'])], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, QM))], 'readdcld', '( %s -> %s e. RR )' % (A0, CB1))
    awb = w.s([w.s([awm], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (Am, AW, CHW('m'))), chwabs(w, Am, 'm', nxm, mn, nnm)], 'eqbrtrd',
              '( %s -> ( abs ` ( %s ` m ) ) <_ %s )' % (Am, AW, CB1))
    CFBX = '( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (AW, CB1, AW, CB1)
    cfb = w.s([fq, cbr, w.s([awb], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (A0, AW, CB1))], '3jca', '( %s -> %s )' % (A0, CFBX))
    # the partial sums
    def axsum(ante, k, nxk, nnk):
        Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (ante, k)
        inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, k)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
        v, _ = mptval(w, Ai, 'q', 'NN', CHW('q'), 'i', inn, mp=AW)
        return w.s([v], 'sumeq2dv', '( %s -> sum_ i e. ( 1 ... %s ) ( %s ` i ) = %s )' % (ante, k, AW, PSW(k)))
    ps = axsum(Am, 'm', nxm, nnm)
    wb = w.s([w.s([nxm, w.s([mn], 'nnnn0d', '( %s -> m e. NN0 )' % Am)], 'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (Am, NX)), w.inst('zl1wbnd')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (Am, PSW('m'), BW))
    wb2 = w.s([w.s([ps], 'fveq2d', '( %s -> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) = ( abs ` %s ) )' % (Am, AW, PSW('m'))), wb], 'eqbrtrd',
              '( %s -> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ %s )' % (Am, AW, BW))
    bwr = w.s([w.s([d['nn']], 'nnred', '( %s -> N e. RR )' % A0), cbr], 'remulcld', '( %s -> %s e. RR )' % (A0, BW))
    ABSPX = '( %s e. RR /\\ A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ %s )' % (BW, AW, BW)
    pack = w.s([w.s([cfb, zp], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX, ZP1)), w.s([bwr, w.s([wb2], 'ralrimiva', '( %s -> A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ %s )' % (A0, AW, BW))],
                                                                                     'jca', '( %s -> %s )' % (A0, ABSPX))], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ %s ) )' % (A0, CFBX, ZP1, ABSPX))
    ATMX = '( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s )' % (AW, DLT('k', 'Z'))
    ag = w.s([pack, w.inst('abagr')], 'syl', '( %s -> sum_ k e. NN %s = sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) )' % (A0, ATMX, AW))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)); nnk = w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Ak)
    lhs = w.s([w.s([axsum(Ak, 'k', nxk, nnk)], 'oveq1d', '( %s -> %s = ( %s x. %s ) )' % (Ak, ATMX, PSW('k'), DLT('k', 'Z')))], 'sumeq2dv',
              '( %s -> sum_ k e. NN %s = %s )' % (A0, ATMX, AB('Z')))
    awk, _ = mptval(w, Ak, 'q', 'NN', CHW('q'), 'k', kn, mp=AW)
    rhs = w.s([w.s([awk], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( %s x. ( k ^c -u Z ) ) )' % (Ak, AW, CHW('k')))], 'sumeq2dv',
              '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )' % (A0, AW, CHW('k')))
    w.qed([w.s([lhs, ag], 'eqtr3d', '( %s -> %s = sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) )' % (A0, AB('Z'), AW)), rhs], 'eqtrd',
          '( %s -> %s = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )' % (A0, AB('Z'), CHW('k')))
    go(w)
