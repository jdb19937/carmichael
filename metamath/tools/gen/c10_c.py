"""Sortie C10: Jensen's inequality from a factorisation, by maximum modulus
on a square with Blaschke numerators (jenbl)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
import congr as _cg
from c10_freeze import S as FS, JX1, JX2, JX3
from c8_n import sqparts, sqre_at
from c8_o import center_int, sqab_st
from c9_f import fac_at, ns_facts
import lin
lin.FASTPATH = True

MS = '( s e. CC |-> %s )' % PBL('s')
MPD = '( s e. D |-> %s )' % PBL('s')
GB = '( ( %s ` z ) x. ( H ` z ) )' % MPD
G = '( z e. D |-> %s )' % GB


def pexs(w, ante, T):
    ex = w.s([], 'prodex', '%s e. _V' % PBL(T))
    return w.s([ex], 'a1i', '( %s -> %s e. _V )' % (ante, PBL(T)))


def gval(w, ante, T, tst):
    """( ante -> ( G ` T ) = ( PBL(T) x. ( H ` T ) ) )"""
    g1, v1 = _cg.mptval(w, ante, 'z', 'D', GB, T, tst, gen=w.g)
    p1, v2 = _cg.mptval(w, ante, 's', 'D', PBL('s'), T, tst, exs=pexs(w, ante, T), gen=w.g)
    assert v2 == PBL(T)
    e = w.s([p1], 'oveq1d', '( %s -> %s = ( %s x. ( H ` %s ) ) )' % (ante, v1, PBL(T), T))
    return w.s([g1, e], 'eqtrd', '( %s -> ( %s ` %s ) = ( %s x. ( H ` %s ) ) )' % (ante, G, T, PBL(T), T))


def gen_jenbl():
    w = W('jenbl', "Jensen's inequality for the multiplicities of a factorisation ` F = prod ( z - q ) ^ O ( q ) x. H ` : when every factored zero lies within ` V ` of ` C ` and ` abs F <_ B ` on the frame of the square of half-side ` R >_ V ` about ` C ` , ` sum O x. log ( R / V ) <_ log ( B / abs F ( C ) ) ` .  Maximum modulus ( ~ rectintmm ) for ` H ` times the Blaschke numerators ( ~ blent , ~ blfr ).")
    A0 = '( %s /\\ %s /\\ %s )' % (JX1, JX2, JX3)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    x1 = s([], 'simp1', JX1); x2 = s([], 'simp2', JX2); x3 = s([], 'simp3', JX3)
    hol = s([x1, w.inst('simpll')], 'syl', HOL)
    zfd = s([x1, w.inst('simplr')], 'syl', '( Z e. Fin /\\ Z C_ D )')
    zf = s([zfd, w.inst('simpl')], 'syl', 'Z e. Fin'); zd = s([zfd, w.inst('simpr')], 'syl', 'Z C_ D')
    of = s([x1, w.inst('simprll')], 'syl', 'O : Z --> NN')
    holh = s([x1, w.inst('simprlr')], 'syl', HOLG('H', 'D'))
    fac = s([x1, w.inst('simprr')], 'syl', FACQ)
    x2a = s([x2, w.inst('simpl')], 'syl', '( C e. CC /\\ R e. RR+ /\\ %s C_ D )' % SQ('C', 'R'))
    x2b = s([x2, w.inst('simpr')], 'syl', '( V e. RR+ /\\ V <_ R /\\ A. j e. Z ( abs ` ( C - j ) ) <_ V )')
    cs = s([x2a, w.inst('simp1')], 'syl', 'C e. CC'); rp = s([x2a, w.inst('simp2')], 'syl', 'R e. RR+')
    sqd = s([x2a, w.inst('simp3')], 'syl', '%s C_ D' % SQ('C', 'R'))
    vp = s([x2b, w.inst('simp1')], 'syl', 'V e. RR+'); vr = s([x2b, w.inst('simp2')], 'syl', 'V <_ R')
    hj = s([x2b, w.inst('simp3')], 'syl', 'A. j e. Z ( abs ` ( C - j ) ) <_ V')
    bst = s([x3, w.inst('simpll')], 'syl', 'B e. RR')
    bfr = s([x3, w.inst('simplr')], 'syl', 'A. u e. %s ( abs ` ( F ` u ) ) <_ B' % FRM('C', 'R'))
    fc0 = s([x3, w.inst('simpr')], 'syl', '( F ` C ) =/= 0')
    dcc = s([s([hol, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )'), w.inst('cncfrss')], 'syl', 'D C_ CC')
    zc = s([zd, dcc], 'sstrd', 'Z C_ CC')
    rr = s([rp], 'rpred', 'R e. RR'); rc = s([rr], 'recnd', 'R e. CC'); r0 = s([rp], 'rpgt0d', '0 < R')
    # g holomorphic
    ent = s([s([s([zf, zc, of], '3jca', '( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN )'), s([cs, rp], 'jca', '( C e. CC /\\ R e. RR+ )')], 'jca',
               '( ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN ) /\\ ( C e. CC /\\ R e. RR+ ) )'), w.inst('blent')], 'syl', ENT(MS))
    dop = s([hol, w.inst('holopn')], 'syl', 'D e. ( TopOpen ` CCfld )')
    hp = s([s([ent, dop], 'jca', '( %s /\\ D e. ( TopOpen ` CCfld ) )' % ENT(MS)), w.inst('zl2hent')], 'syl', HOLG(MPD, 'D'))
    hg = s([s([hp, holh], 'jca', '( %s /\\ %s )' % (HOLG(MPD, 'D'), HOLG('H', 'D'))), w.inst('holmul')], 'syl', HOLG(G, 'D'))
    # the square
    a, b = SQA('C', 'R'), SQB('C', 'R')
    ab = sqab_st(w, A0, cs, rr, 'C', 'R')
    intc = center_int(w, A0, cs, rr, r0, 'C', 'R')
    csq = w.s([ab, intc, w.inst('crectinp')], 'syl2anc', '( %s -> C e. %s )' % (A0, SQ('C', 'R')))
    cd = s([sqd, csq], 'sseldd', 'C e. D')
    frp = w.s([ab, intc, w.inst('crectfrp')], 'syl2anc', '( %s -> %s C_ ( %s \\ { C } ) )' % (A0, FRM('C', 'R'), SQ('C', 'R')))
    pa = sqparts(w, A0, sqre_at(w, A0, cs, rr))
    rec = s([cs], 'recld', '( Re ` C ) e. RR'); imc = s([cs], 'imcld', '( Im ` C ) e. RR')
    lv = {'( Re ` C )': rec, '( Im ` C )': imc, 'R': rr,
          '( Re ` %s )' % a: s([s([ab, w.inst('simpl')], 'syl', '%s e. CC' % a)], 'recld', '( Re ` %s ) e. RR' % a),
          '( Re ` %s )' % b: s([s([ab, w.inst('simpr')], 'syl', '%s e. CC' % b)], 'recld', '( Re ` %s ) e. RR' % b),
          '( Im ` %s )' % a: s([s([ab, w.inst('simpl')], 'syl', '%s e. CC' % a)], 'imcld', '( Im ` %s ) e. RR' % a),
          '( Im ` %s )' % b: s([s([ab, w.inst('simpr')], 'syl', '%s e. CC' % b)], 'imcld', '( Im ` %s ) e. RR' % b)}
    q1 = lin8(w, A0, [pa[0]], 'R <_ ( ( Re ` C ) - ( Re ` %s ) )' % a, lv)
    q2 = lin8(w, A0, [pa[1]], 'R <_ ( ( Re ` %s ) - ( Re ` C ) )' % b, lv)
    q3 = lin8(w, A0, [pa[2]], 'R <_ ( ( Im ` C ) - ( Im ` %s ) )' % a, lv)
    q4 = lin8(w, A0, [pa[3]], 'R <_ ( ( Im ` %s ) - ( Im ` C ) )' % b, lv)
    RB = RBDG(a, b, 'C', 'R')
    rbd = s([rr, s([s([q1, q2], 'jca', '( R <_ ( ( Re ` C ) - ( Re ` %s ) ) /\\ R <_ ( ( Re ` %s ) - ( Re ` C ) ) )' % (a, b)),
                    s([q3, q4], 'jca', '( R <_ ( ( Im ` C ) - ( Im ` %s ) ) /\\ R <_ ( ( Im ` %s ) - ( Im ` C ) ) )' % (a, b))], 'jca', RB[len('( R e. RR /\\ '):-2])], 'jca', RB)
    dall = w.s([ab, intc, rbd, w.inst('crectdis')], 'syl3anc', '( %s -> A. u e. %s R <_ ( abs ` ( u - C ) ) )' % (A0, FRM('C', 'R')))
    # ---- the frame: abs g ( x ) <_ B
    A4 = '( %s /\\ x e. %s )' % (A0, FRM('C', 'R'))
    s4 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A4, f))
    L4 = lambda st: lift(w, st, A4)
    xf = s4([], 'simpr', 'x e. %s' % FRM('C', 'R'))
    xsq = s4([s4([L4(frp), xf], 'sseldd', 'x e. ( %s \\ { C } )' % SQ('C', 'R'))], 'eldifad', 'x e. %s' % SQ('C', 'R'))
    xd = s4([L4(sqd), xsq], 'sseldd', 'x e. D'); xc = s4([L4(dcc), xd], 'sseldd', 'x e. CC')
    subu = lambda f: w.s([w.s([w.s([], 'oveq1' if 'u -' in f else 'fveq2', '( u = x -> %s )' % f)], 'fveq2d' if 'u -' in f else 'fveq2d',
                              '( u = x -> ( abs ` ( u - C ) ) = ( abs ` ( x - C ) ) )')], 'breq2d', '( u = x -> ( R <_ ( abs ` ( u - C ) ) <-> R <_ ( abs ` ( x - C ) ) ) )')
    xdist = s4([subu('( u - C ) = ( x - C )'), L4(dall), xf], 'rspcdva', 'R <_ ( abs ` ( x - C ) )')
    sb = w.s([w.s([w.s([], 'fveq2', '( u = x -> ( F ` u ) = ( F ` x ) )')], 'fveq2d', '( u = x -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` x ) ) )')], 'breq1d',
             '( u = x -> ( ( abs ` ( F ` u ) ) <_ B <-> ( abs ` ( F ` x ) ) <_ B ) )')
    xfb = s4([sb, L4(bfr), xf], 'rspcdva', '( abs ` ( F ` x ) ) <_ B')
    # termwise
    A5 = '( %s /\\ k e. Z )' % A4
    s5 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A5, f))
    L5 = lambda st: lift(w, st, A5)
    kz = s5([], 'simpr', 'k e. Z'); kc = s5([L5(zc), kz], 'sseldd', 'k e. CC')
    ok = s5([L5(of), kz], 'ffvelcdmd', '( O ` k ) e. NN'); ok0 = s5([ok], 'nnnn0d', '( O ` k ) e. NN0')
    sj = w.s([w.s([w.s([], 'oveq2', '( j = k -> ( C - j ) = ( C - k ) )')], 'fveq2d', '( j = k -> ( abs ` ( C - j ) ) = ( abs ` ( C - k ) ) )')], 'breq1d',
             '( j = k -> ( ( abs ` ( C - j ) ) <_ V <-> ( abs ` ( C - k ) ) <_ V ) )')
    kv = s5([sj, L5(hj), kz], 'rspcdva', '( abs ` ( C - k ) ) <_ V')
    kab = s5([kc, L5(cs)], 'abssubd', '( abs ` ( k - C ) ) = ( abs ` ( C - k ) )')
    kvr = s5([kab, kv], 'eqbrtrd', '( abs ` ( k - C ) ) <_ V')
    vrr = s5([L5(vp)], 'rpred', 'V e. RR')
    akc = s5([s5([kc, L5(cs)], 'subcld', '( k - C ) e. CC')], 'abscld', '( abs ` ( k - C ) ) e. RR')
    kR = s5([akc, vrr, L5(rr), kvr, L5(vr)], 'letrd', '( abs ` ( k - C ) ) <_ R')
    BK = BLF('k', 'x')
    bl = tsub(FS['blfr'], {'Q': 'k', 'U': 'x'})
    bla, blc = ante_of(bl)
    bk = s5([s5([s5([L5(cs), L5(rp)], 'jca', '( C e. CC /\\ R e. RR+ )'), s5([kc, kR], 'jca', '( k e. CC /\\ ( abs ` ( k - C ) ) <_ R )'),
                  s5([L5(xc), L5(xdist)], 'jca', '( x e. CC /\\ R <_ ( abs ` ( x - C ) ) )')], '3jca', bla), w.inst('blfr')], 'syl', blc)
    bkc = s5([L5(rc), s5([s5([s5([s5([kc, L5(cs)], 'subcld', '( k - C ) e. CC')], 'cjcld', '( * ` ( k - C ) ) e. CC'), L5(rc), s5([L5(rp)], 'rpne0d', 'R =/= 0')], 'divcld',
                              '( ( * ` ( k - C ) ) / R ) e. CC'), s5([L5(xc), L5(cs)], 'subcld', '( x - C ) e. CC')], 'mulcld',
                         '( ( ( * ` ( k - C ) ) / R ) x. ( x - C ) ) e. CC')], 'subcld', '%s e. CC' % BK)
    xk = s5([L5(xc), kc], 'subcld', '( x - k ) e. CC')
    abk = s5([bkc], 'abscld', '( abs ` %s ) e. RR' % BK); axk = s5([xk], 'abscld', '( abs ` ( x - k ) ) e. RR')
    le1 = s5([s5([s5([abk, axk, ok0], '3jca', '( ( abs ` %s ) e. RR /\\ ( abs ` ( x - k ) ) e. RR /\\ ( O ` k ) e. NN0 )' % BK),
                  s5([s5([bkc], 'absge0d', '0 <_ ( abs ` %s )' % BK), bk], 'jca', '( 0 <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ ( abs ` ( x - k ) ) )' % (BK, BK))], 'jca',
                 '( ( ( abs ` %s ) e. RR /\\ ( abs ` ( x - k ) ) e. RR /\\ ( O ` k ) e. NN0 ) /\\ ( 0 <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ ( abs ` ( x - k ) ) ) )' % (BK, BK, BK)),
              w.inst('leexp1a')], 'syl', '( ( abs ` %s ) ^ ( O ` k ) ) <_ ( ( abs ` ( x - k ) ) ^ ( O ` k ) )' % BK)
    TB, TZ = '( %s ^ ( O ` k ) )' % BK, '( ( x - k ) ^ ( O ` k ) )'
    e1 = s5([bkc, ok0], 'absexpd', '( abs ` %s ) = ( ( abs ` %s ) ^ ( O ` k ) )' % (TB, BK))
    e2 = s5([xk, ok0], 'absexpd', '( abs ` %s ) = ( ( abs ` ( x - k ) ) ^ ( O ` k ) )' % TZ)
    tle = s5([s5([e1, le1], 'eqbrtrd', '( abs ` %s ) <_ ( ( abs ` ( x - k ) ) ^ ( O ` k ) )' % TB), e2], 'breqtrrd', '( abs ` %s ) <_ ( abs ` %s )' % (TB, TZ))
    tbc = s5([bkc, ok0], 'expcld', '%s e. CC' % TB); tzc = s5([xk, ok0], 'expcld', '%s e. CC' % TZ)
    nf = w.s([], 'nfv', 'F/ k %s' % A4)
    zf4 = L4(zf)
    PA = 'prod_ k e. Z ( abs ` %s )' % TB
    PZ = 'prod_ k e. Z ( abs ` %s )' % TZ
    ple = s4([nf, zf4, s5([tbc], 'abscld', '( abs ` %s ) e. RR' % TB), s5([tbc], 'absge0d', '0 <_ ( abs ` %s )' % TB), s5([tzc], 'abscld', '( abs ` %s ) e. RR' % TZ), tle],
             'fprodle', '%s <_ %s' % (PA, PZ))
    pab = s4([zf4, tbc], 'z5fprodabs', '( abs ` %s ) = %s' % (PBL('x'), PA))
    PZK = 'prod_ k e. Z %s' % TZ
    pzb = s4([zf4, tzc], 'z5fprodabs', '( abs ` %s ) = %s' % (PZK, PZ))
    pl = s4([s4([pab, ple], 'eqbrtrd', '( abs ` %s ) <_ %s' % (PBL('x'), PZ)), pzb], 'breqtrrd', '( abs ` %s ) <_ ( abs ` %s )' % (PBL('x'), PZK))
    # multiply by abs H ( x )
    HX = '( H ` x )'
    hf = L4(s([holh, w.inst('simpl')], 'syl', 'H e. ( D -cn-> CC )'))
    hxc = s4([s4([hf, w.inst('cncff')], 'syl', 'H : D --> CC'), xd], 'ffvelcdmd', '%s e. CC' % HX)
    pxc = s4([zf4, tbc], 'fprodcl', '%s e. CC' % PBL('x'))
    pzc = s4([zf4, tzc], 'fprodcl', '%s e. CC' % PZK)
    ml = s4([s4([pxc], 'abscld', '( abs ` %s ) e. RR' % PBL('x')), s4([pzc], 'abscld', '( abs ` %s ) e. RR' % PZK), s4([hxc], 'abscld', '( abs ` %s ) e. RR' % HX),
             s4([hxc], 'absge0d', '0 <_ ( abs ` %s )' % HX), pl], 'lemul1ad',
            '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( abs ` %s ) x. ( abs ` %s ) )' % (PBL('x'), HX, PZK, HX))
    gx = gval(w, A4, 'x', xd)
    ag = s4([s4([gx], 'fveq2d', '( abs ` ( %s ` x ) ) = ( abs ` ( %s x. %s ) )' % (G, PBL('x'), HX)), s4([pxc, hxc], 'absmuld',
            '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PBL('x'), HX, PBL('x'), HX))], 'eqtrd',
            '( abs ` ( %s ` x ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (G, PBL('x'), HX))
    # F ( x ) with index k
    fx = fac_at(w, A4, L4(fac), 'x', xd)
    PZQ = PRZ('Z', 'x')
    st, new = subst_eq(w, '( ( x - q ) ^ ( O ` q ) )', 'q', 'k')
    cb = w.s([st], 'cbvprodv', '%s = %s' % (PZQ, PZK))
    fx2 = s4([fx, s4([s4([cb], 'a1i', '%s = %s' % (PZQ, PZK))], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (PZQ, HX, PZK, HX))], 'eqtrd',
             '( F ` x ) = ( %s x. %s )' % (PZK, HX))
    af = s4([s4([fx2], 'fveq2d', '( abs ` ( F ` x ) ) = ( abs ` ( %s x. %s ) )' % (PZK, HX)), s4([pzc, hxc], 'absmuld',
            '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PZK, HX, PZK, HX))], 'eqtrd',
            '( abs ` ( F ` x ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PZK, HX))
    gle = s4([s4([ag, ml], 'eqbrtrd', '( abs ` ( %s ` x ) ) <_ ( ( abs ` %s ) x. ( abs ` %s ) )' % (G, PZK, HX)), af], 'breqtrrd', '( abs ` ( %s ` x ) ) <_ ( abs ` ( F ` x ) )' % G)
    gcn = L4(s([hg, w.inst('simpl')], 'syl', '%s e. ( D -cn-> CC )' % G))
    gb = s4([s4([gcn, w.inst('cncff')], 'syl', '%s : D --> CC' % G), xd], 'ffvelcdmd', '( %s ` x ) e. CC' % G)
    gbr = s4([gb], 'abscld', '( abs ` ( %s ` x ) ) e. RR' % G)
    fxr = s4([s4([s4([s4([L4(hol), w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )'), w.inst('cncff')], 'syl', 'F : D --> CC'), xd], 'ffvelcdmd', '( F ` x ) e. CC')], 'abscld',
             '( abs ` ( F ` x ) ) e. RR')
    gxb = s4([gbr, fxr, L4(bst), gle, xfb], 'letrd', '( abs ` ( %s ` x ) ) <_ B' % G)
    gall = s([gxb], 'ralrimiva', 'A. x e. %s ( abs ` ( %s ` x ) ) <_ B' % (FRM('C', 'R'), G))
    # maximum modulus at C
    rm = tsub(stmt('rectintmm'), {'A': a, 'B': b, 'P': 'C', 'F': G, 'M': 'B', 'u': 'x'})
    rma, rmc = ante_of(rm)
    intcp = intc
    p1_, p2_ = top_and(rma)
    gC = s([s([ab, intcp, s([hg, sqd], 'jca', '( %s /\\ %s C_ D )' % (HOLG(G, 'D'), SQ('C', 'R')))], '3jca', p1_),
            s([bst, gall], 'jca', p2_)], 'jca', rma)
    gCb = s([gC, w.inst('rectintmm')], 'syl', rmc)
    # ---- the centre
    gc = gval(w, A0, 'C', cd)
    A1 = '( %s /\\ k e. Z )' % A0
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L1 = lambda st: lift(w, st, A1)
    kz = s1([], 'simpr', 'k e. Z'); kc = s1([L1(zc), kz], 'sseldd', 'k e. CC')
    ok = s1([L1(of), kz], 'ffvelcdmd', '( O ` k ) e. NN')
    K = '( ( * ` ( k - C ) ) / R )'
    Kc = s1([s1([s1([kc, L1(cs)], 'subcld', '( k - C ) e. CC')], 'cjcld', '( * ` ( k - C ) ) e. CC'), L1(rc), s1([L1(rp)], 'rpne0d', 'R =/= 0')], 'divcld', '%s e. CC' % K)
    t1 = s1([s1([s1([L1(cs)], 'subidd', '( C - C ) = 0')], 'oveq2d', '( %s x. ( C - C ) ) = ( %s x. 0 )' % (K, K)), s1([Kc], 'mul01d', '( %s x. 0 ) = 0' % K)], 'eqtrd',
            '( %s x. ( C - C ) ) = 0' % K)
    t2 = s1([s1([t1], 'oveq2d', '%s = ( R - 0 )' % BLF('k', 'C')), s1([L1(rc)], 'subid1d', '( R - 0 ) = R')], 'eqtrd', '%s = R' % BLF('k', 'C'))
    t3 = s1([t2], 'oveq1d', '( %s ^ ( O ` k ) ) = ( R ^ ( O ` k ) )' % BLF('k', 'C'))
    okz = s1([ok], 'nnzd', '( O ` k ) e. ZZ')
    t4 = s1([s1([L1(rp), okz], 'jca', '( R e. RR+ /\\ ( O ` k ) e. ZZ )'), w.inst('reexplog')], 'syl', '( R ^ ( O ` k ) ) = ( exp ` ( ( O ` k ) x. ( log ` R ) ) )')
    BT = '( exp ` ( ( O ` k ) x. ( log ` R ) ) )'
    pc1 = s([s1([t3, t4], 'eqtrd', '( %s ^ ( O ` k ) ) = %s' % (BLF('k', 'C'), BT))], 'prodeq2dv', '%s = prod_ k e. Z %s' % (PBL('C'), BT))
    MP = '( x e. Z |-> ( ( O ` x ) x. ( log ` R ) ) )'
    fv, val = _cg.mptval(w, A1, 'x', 'Z', '( ( O ` x ) x. ( log ` R ) )', 'k', kz, gen=w.g)
    assert val == '( ( O ` k ) x. ( log ` R ) )', val
    lrc = s1([s1([L1(rp)], 'relogcld', '( log ` R ) e. RR')], 'recnd', '( log ` R ) e. CC')
    okc = s1([ok], 'nncnd', '( O ` k ) e. CC')
    fvc = s1([fv, s1([okc, lrc], 'mulcld', '%s e. CC' % val)], 'eqeltrd', '( %s ` k ) e. CC' % MP)
    pe = s([zf, fvc], 'fprodefsumfi', 'prod_ k e. Z ( exp ` ( %s ` k ) ) = ( exp ` sum_ k e. Z ( %s ` k ) )' % (MP, MP))
    p1 = s([s1([fv], 'fveq2d', '( exp ` ( %s ` k ) ) = %s' % (MP, BT))], 'prodeq2dv', 'prod_ k e. Z ( exp ` ( %s ` k ) ) = prod_ k e. Z %s' % (MP, BT))
    sm1 = s([fv], 'sumeq2dv', 'sum_ k e. Z ( %s ` k ) = sum_ k e. Z ( ( O ` k ) x. ( log ` R ) )' % MP)
    lr0 = s([s([rp], 'relogcld', '( log ` R ) e. RR')], 'recnd', '( log ` R ) e. CC')
    NSK = 'sum_ k e. Z ( O ` k )'
    sm2 = s([zf, lr0, okc], 'fsummulc1', '( %s x. ( log ` R ) ) = sum_ k e. Z ( ( O ` k ) x. ( log ` R ) )' % NSK)
    NS = NSUM('Z')
    stq, newq = subst_eq(w, '( O ` k )', 'k', 'q')
    cbs = s([w.s([stq], 'cbvsumv', '%s = %s' % (NSK, NS))], 'a1i', '%s = %s' % (NSK, NS))
    sm3 = s([s([sm1, sm2], 'eqtr4d', 'sum_ k e. Z ( %s ` k ) = ( %s x. ( log ` R ) )' % (MP, NSK)), s([cbs], 'oveq1d', '( %s x. ( log ` R ) ) = ( %s x. ( log ` R ) )' % (NSK, NS))],
             'eqtrd', 'sum_ k e. Z ( %s ` k ) = ( %s x. ( log ` R ) )' % (MP, NS))
    EXR = '( exp ` ( %s x. ( log ` R ) ) )' % NS
    pC = s([pc1, s([s([p1, pe], 'eqtr3d', 'prod_ k e. Z %s = ( exp ` sum_ k e. Z ( %s ` k ) )' % (BT, MP)), s([sm3], 'fveq2d', '( exp ` sum_ k e. Z ( %s ` k ) ) = %s' % (MP, EXR))],
                   'eqtrd', 'prod_ k e. Z %s = %s' % (BT, EXR))], 'eqtrd', '%s = %s' % (PBL('C'), EXR))
    nsr, nsg = ns_facts(w, A0, zf, of)
    lr = s([rp], 'relogcld', '( log ` R ) e. RR'); lv = s([vp], 'relogcld', '( log ` V ) e. RR')
    exr = s([s([nsr, lr], 'remulcld', '( %s x. ( log ` R ) ) e. RR' % NS)], 'rpefcld', '%s e. RR+' % EXR)
    # abs G ( C ) = EXR abs H ( C )
    HC = '( H ` C )'
    hcc = s([s([s([holh, w.inst('simpl')], 'syl', 'H e. ( D -cn-> CC )'), w.inst('cncff')], 'syl', 'H : D --> CC'), cd], 'ffvelcdmd', '%s e. CC' % HC)
    agc = s([s([gc], 'fveq2d', '( abs ` ( %s ` C ) ) = ( abs ` ( %s x. %s ) )' % (G, PBL('C'), HC)),
             s([s([s([pC], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (PBL('C'), HC, EXR, HC))], 'fveq2d', '( abs ` ( %s x. %s ) ) = ( abs ` ( %s x. %s ) )' % (PBL('C'), HC, EXR, HC)),
                s([s([exr], 'rpcnd', '%s e. CC' % EXR), hcc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (EXR, HC, EXR, HC))], 'eqtrd',
               '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PBL('C'), HC, EXR, HC))], 'eqtrd', '( abs ` ( %s ` C ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (G, EXR, HC))
    aex = s([s([exr], 'rpred', '%s e. RR' % EXR), s([exr], 'rpge0d', '0 <_ %s' % EXR)], 'absidd', '( abs ` %s ) = %s' % (EXR, EXR))
    agc2 = s([agc, s([aex], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (EXR, HC, EXR, HC))], 'eqtrd',
             '( abs ` ( %s ` C ) ) = ( %s x. ( abs ` %s ) )' % (G, EXR, HC))
    up = s([agc2, gCb], 'eqbrtrrd', '( %s x. ( abs ` %s ) ) <_ B' % (EXR, HC))
    # F ( C ) = PRZ x. H ( C ); H ( C ) =/= 0
    fcq = fac_at(w, A0, fac, 'C', cd)
    PZC = PRZ('Z', 'C')
    pzc = s([zf, s1([s1([L1(cs), kc], 'subcld', '( C - k ) e. CC'), s1([ok], 'nnnn0d', '( O ` k ) e. NN0')], 'expcld', '( ( C - k ) ^ ( O ` k ) ) e. CC')], 'fprodcl',
            'prod_ k e. Z ( ( C - k ) ^ ( O ` k ) ) e. CC')
    stc, newc = subst_eq(w, '( ( C - k ) ^ ( O ` k ) )', 'k', 'q')
    cbc = s([w.s([stc], 'cbvprodv', 'prod_ k e. Z ( ( C - k ) ^ ( O ` k ) ) = %s' % PZC)], 'a1i', 'prod_ k e. Z ( ( C - k ) ^ ( O ` k ) ) = %s' % PZC)
    pzc = s([cbc, pzc], 'eqeltrrd', '%s e. CC' % PZC)
    prn = s([fcq], 'neeq1d', '( ( F ` C ) =/= 0 <-> ( %s x. %s ) =/= 0 )' % (PZC, HC))
    prn = s([fc0, prn], 'mpbid', '( %s x. %s ) =/= 0' % (PZC, HC))
    both = s([pzc, hcc, w.inst('mulne0b')], 'syl2anc', '( ( %s =/= 0 /\\ %s =/= 0 ) <-> ( %s x. %s ) =/= 0 )' % (PZC, HC, PZC, HC))
    hc0 = s([s([prn, both], 'mpbird', '( %s =/= 0 /\\ %s =/= 0 )' % (PZC, HC))], 'simprd', '%s =/= 0' % HC)
    ahp = s([hcc, hc0], 'absrpcld', '( abs ` %s ) e. RR+' % HC)
    afp = s([s([s([s([hol, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )'), w.inst('cncff')], 'syl', 'F : D --> CC'), cd], 'ffvelcdmd', '( F ` C ) e. CC'), fc0], 'absrpcld',
            '( abs ` ( F ` C ) ) e. RR+')
    # abs F ( C ) <_ EXV abs H ( C )
    PH0 = '( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 )'
    of0 = s([of, w.s([w.s([], 'nnssnn0', 'NN C_ NN0')], 'a1i', '( %s -> NN C_ NN0 )' % A0)], 'fssd', 'O : Z --> NN0')
    fu = tsub(stmt('fprodube'), {'S': 'Z', 'U': 'C', 'R': 'V'})
    fua, fuc = ante_of(fu)
    ub = s([s([s([zf, zc, of0], '3jca', PH0), s([cs, vp, hj], '3jca', '( C e. CC /\\ V e. RR+ /\\ A. j e. Z ( abs ` ( C - j ) ) <_ V )')], 'jca', fua), w.inst('fprodube')], 'syl', fuc)
    EXV = '( exp ` ( %s x. ( log ` V ) ) )' % NS
    exv = s([s([nsr, lv], 'remulcld', '( %s x. ( log ` V ) ) e. RR' % NS)], 'rpefcld', '%s e. RR+' % EXV)
    afc = s([s([fcq], 'fveq2d', '( abs ` ( F ` C ) ) = ( abs ` ( %s x. %s ) )' % (PZC, HC)), s([pzc, hcc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PZC, HC, PZC, HC))],
            'eqtrd', '( abs ` ( F ` C ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PZC, HC))
    ahr = s([ahp], 'rpred', '( abs ` %s ) e. RR' % HC)
    lo = s([s([pzc], 'abscld', '( abs ` %s ) e. RR' % PZC), s([exv], 'rpred', '%s e. RR' % EXV), ahr, s([ahp], 'rpge0d', '0 <_ ( abs ` %s )' % HC), ub], 'lemul1ad',
           '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( %s x. ( abs ` %s ) )' % (PZC, HC, EXV, HC))
    lo = s([afc, lo], 'eqbrtrd', '( abs ` ( F ` C ) ) <_ ( %s x. ( abs ` %s ) )' % (EXV, HC))
    # logs
    M1 = '( %s x. ( abs ` %s ) )' % (EXR, HC)
    m1p = s([exr, ahp], 'rpmulcld', '%s e. RR+' % M1)
    bpos = s([s([], '0red', '0 e. RR'), s([m1p], 'rpred', '%s e. RR' % M1), bst, s([m1p], 'rpgt0d', '0 < %s' % M1), up], 'ltletrd', '0 < B')
    bp = s([bst, bpos], 'elrpd', 'B e. RR+')
    HC_ = '( abs ` %s )' % HC
    AF = '( abs ` ( F ` C ) )'
    LR, LV, LB, LH, LF = '( log ` R )', '( log ` V )', '( log ` B )', '( log ` %s )' % HC_, '( log ` %s )' % AF
    l1 = s([up, s([m1p, bp], 'logled', '( %s <_ B <-> ( log ` %s ) <_ %s )' % (M1, M1, LB))], 'mpbid', '( log ` %s ) <_ %s' % (M1, LB))
    NR, NV = '( %s x. %s )' % (NS, LR), '( %s x. %s )' % (NS, LV)
    e1 = s([s([exr, ahp], 'relogmuld', '( log ` %s ) = ( ( log ` %s ) + %s )' % (M1, EXR, LH)),
            s([s([s([nsr, lr], 'remulcld', '%s e. RR' % NR), w.inst('relogef')], 'syl', '( log ` %s ) = %s' % (EXR, NR))], 'oveq1d',
              '( ( log ` %s ) + %s ) = ( %s + %s )' % (EXR, LH, NR, LH))], 'eqtrd', '( log ` %s ) = ( %s + %s )' % (M1, NR, LH))
    M2 = '( %s x. %s )' % (EXV, HC_)
    m2p = s([exv, ahp], 'rpmulcld', '%s e. RR+' % M2)
    l2 = s([lo, s([afp, m2p], 'logled', '( %s <_ %s <-> %s <_ ( log ` %s ) )' % (AF, M2, LF, M2))], 'mpbid', '%s <_ ( log ` %s )' % (LF, M2))
    e2 = s([s([exv, ahp], 'relogmuld', '( log ` %s ) = ( ( log ` %s ) + %s )' % (M2, EXV, LH)),
            s([s([s([nsr, lv], 'remulcld', '%s e. RR' % NV), w.inst('relogef')], 'syl', '( log ` %s ) = %s' % (EXV, NV))], 'oveq1d',
              '( ( log ` %s ) + %s ) = ( %s + %s )' % (EXV, LH, NV, LH))], 'eqtrd', '( log ` %s ) = ( %s + %s )' % (M2, NV, LH))
    lvs = {'( log ` %s )' % M1: s([m1p], 'relogcld', '( log ` %s ) e. RR' % M1), '( log ` %s )' % M2: s([m2p], 'relogcld', '( log ` %s ) e. RR' % M2),
           LB: s([bp], 'relogcld', '%s e. RR' % LB), LF: s([afp], 'relogcld', '%s e. RR' % LF), LH: s([ahp], 'relogcld', '%s e. RR' % LH),
           NS: nsr, LR: lr, LV: lv}
    import cl as _cl
    c = _cl.Closure(w, A0, {})
    for a_, st_ in lvs.items():
        c.leaf(a_, 'RR', st_)
    core = lin.linarith(w, A0, [l1, e1, l2, e2], '( %s x. ( %s - %s ) ) <_ ( %s - %s )' % (NS, LR, LV, LB, LF), closure=c, products=True)
    eg = s([s([rp, vp], 'relogdivd', '( log ` ( R / V ) ) = ( %s - %s )' % (LR, LV))], 'oveq2d', '( %s x. ( log ` ( R / V ) ) ) = ( %s x. ( %s - %s ) )' % (NS, NS, LR, LV))
    er = s([bp, afp], 'relogdivd', '( log ` ( B / %s ) ) = ( %s - %s )' % (AF, LB, LF))
    goal = '( %s -> ( %s x. ( log ` ( R / V ) ) ) <_ ( log ` ( B / %s ) ) )' % (A0, NS, AF)
    assert goal == FS['jenbl'], goal
    w.qed([s([eg, core], 'eqbrtrd', '( %s x. ( log ` ( R / V ) ) ) <_ ( %s - %s )' % (NS, LB, LF)), er], 'breqtrrd', goal)
    return run8(w)
    return w, A0, s, dict(up=up, lo=lo, exr=exr, exv=exv, ahp=ahp, afp=afp, bp=bp, nsr=nsr, lr=lr, lv=lv, rp=rp, vp=vp, M1=M1, m1p=m1p, EXR=EXR, EXV=EXV, HC=HC, NS=NS)


if __name__ == '__main__':
    gen_jenbl()
