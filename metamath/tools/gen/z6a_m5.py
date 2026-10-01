"""Z6a (block D): the line shifts (z6mstep, z6mvlr, z6mvll, z6mright, z6mlt, z6mleft)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_mlib import *
from tm import sub

only = sys.argv[1:]
H = '( 1 / 2 )'
AL = '( -u K - ( 1 / 2 ) )'
BR = '( ( 1 / 2 ) - K )'
M0 = '( ; 6 4 x. ( ( Y ^c ( K + ( 1 / 2 ) ) ) + ( Y ^c ( K - ( 1 / 2 ) ) ) ) )'
M1 = '( ; 6 4 x. ( ( Y ^c -u ( 1 / 2 ) ) + ( Y ^c -u 3 ) ) )'
KR = '( %s x. ( ( -u Y ^ K ) / ( ! ` K ) ) )' % TPI
GBODY = '( ( _G ` w ) x. ( Y ^c -u w ) )'


def want(lab):
    return not only or lab in only


def AIz(z):
    return '( abs ` ( Im ` %s ) )' % z


def imne0(w, A, zc, ge):
    """( A -> ( Im ` z ) =/= 0 ) from ge: ( A -> 1 <_ ( abs ` ( Im ` z ) ) ); zc: z e. CC (text taken from ge)"""
    s = mkst(w, A)
    f = split_imp(formula_of(w, ge))[1]
    z = f[len('1 <_ ( abs ` ( Im ` '):-len(' ) )')]
    imc = s([s([zc], 'imcld', '( Im ` %s ) e. RR' % z)], 'recnd', '( Im ` %s ) e. CC' % z)
    cl = Closure(w, A, {AIz(z): ('RR', s([imc], 'abscld', '%s e. RR' % AIz(z)))})
    gt = linarith(w, A, [ge], '0 < %s' % AIz(z), closure=cl)
    return s([gt, s([imc, w.inst('absgt0')], 'syl', '( ( Im ` %s ) =/= 0 <-> 0 < %s )' % (z, AIz(z)))], 'mpbird', '( Im ` %s ) =/= 0' % z)


def dgim(w, A, zc, ge):
    """( A -> z e. DG ) from | Im z | >_ 1"""
    s = mkst(w, A)
    z = split_imp(formula_of(w, zc))[1][:-len(' e. CC')]
    ne = imne0(w, A, zc, ge)
    return s([zc, s([ne], 'olcd', '( -. ( Re ` %s ) e. ZZ \\/ ( Im ` %s ) =/= 0 )' % (z, z)), w.inst('z6mndg')], 'syl2anc', '%s e. %s' % (z, DG))


def dgre(w, A, zc, re, nz, z):
    """( A -> z e. DG ) from re: ( Re ` z ) = X and nz: -. X e. ZZ"""
    s = mkst(w, A)
    X = split_imp(formula_of(w, re))[1].split(' = ', 1)[1]
    nre = s([nz, s([re], 'eleq1d', '( ( Re ` %s ) e. ZZ <-> %s e. ZZ )' % (z, X))], 'mtbird', '-. ( Re ` %s ) e. ZZ' % z)
    return s([zc, s([nre], 'orcd', '( -. ( Re ` %s ) e. ZZ \\/ ( Im ` %s ) =/= 0 )' % (z, z)), w.inst('z6mndg')], 'syl2anc', '%s e. %s' % (z, DG))


def gyval(w, A, z, zdg):
    """( A -> ( abs ` ( GY ` z ) ) = ( abs ` ( ( _G ` z ) x. ( Y ^c -u z ) ) ) )"""
    s = mkst(w, A)
    v, V = mpval(w, A, 'w', DG, GBODY, z, zdg)
    return s([v], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (GYM, z, V)), V


def e4eq(w, A, eq, X, Y, M):
    """( A -> ( M x. E4(X) ) = ( M x. E4(Y) ) ) from eq: ( A -> X = Y )"""
    s = mkst(w, A)
    a = s([eq], 'oveq1d', '( %s / 4 ) = ( %s / 4 )' % (X, Y))
    b = s([a], 'negeqd', '-u ( %s / 4 ) = -u ( %s / 4 )' % (X, Y))
    c = s([b], 'oveq2d', '%s = %s' % (E4(X), E4(Y)))
    return s([c], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (M, E4(X), M, E4(Y)))


def tpic(w, A):
    s = mkst(w, A)
    return s([a1c(w, A, '2cn', '2 e. CC'), s([a1c(w, A, 'ax-icn', '_i e. CC'), a1c(w, A, 'picn', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)


# ---------------------------------------------------------------- z6mstep
def z6mstep():
    w = W('z6mstep', 'Moving the Mellin line across the pole at ` -u K ` : ` VL ( 1 / 2 - K ) - VL ( -u K - 1 / 2 ) = 2 pi i ( -u Y ) ^ K / K ! ` '
          '( ~ z6shift with the strip majorant ~ z6gyl and the rectangle integrals ~ z6mrect ).')
    A = split_imp(STATEMENTS['z6mstep'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A)
    kr = s([kn], 'nn0red', 'K e. RR')
    cl = Closure(w, A, {'K': ('RR', kr), 'Y': ('RR+', yrp)})
    alr = cl.mem(AL, 'RR'); brr = cl.mem(BR, 'RR')
    ab = s([s([alr, brr], 'jca', '( %s e. RR /\\ %s e. RR )' % (AL, BR)), linarith(w, A, [], '%s < %s' % (AL, BR), closure=cl)], 'jca',
           '( ( %s e. RR /\\ %s e. RR ) /\\ %s < %s )' % (AL, BR, AL, BR))
    gyc = s([s([yrp, w.inst('z6gyhol')], 'syl', HOLG(GYM, DG))], 'simpld', '%s e. ( %s -cn-> CC )' % (GYM, DG))
    nh = s([kn, w.inst('z6mnhz')], 'syl', '( -. %s e. ZZ /\\ -. %s e. ZZ )' % (AL, BR))
    SD = sub(STRIPD, {'A': AL, 'B': BR, 'Y': '1', 'D': DG})
    SM = sub(STRIPM, {'A': AL, 'B': BR, 'Y': '1', 'G': GYM, 'M': M0})
    RNG = '( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ %s )' % (AL, BR)
    DJ = '( ( ( Re ` z ) = %s \\/ ( Re ` z ) = %s ) \\/ 1 <_ %s )' % (AL, BR, AIz('z'))
    # STRIPD
    Az = '( ( %s /\\ z e. CC ) /\\ ( %s /\\ %s ) )' % (A, RNG, DJ)
    t = mkst(w, Az)
    zc = w.s([], 'simplr', '( %s -> z e. CC )' % Az)
    dj = w.s([], 'simprr', '( %s -> %s )' % (Az, DJ))

    def reX(X, nzs):
        Ae = '( %s /\\ ( Re ` z ) = %s )' % (Az, X)
        te = mkst(w, Ae)
        e = w.s([], 'simpr', '( %s -> ( Re ` z ) = %s )' % (Ae, X))
        n = te([lift(w, nzs, Ae), te([e], 'eleq1d', '( ( Re ` z ) e. ZZ <-> %s e. ZZ )' % X)], 'mtbird', '-. ( Re ` z ) e. ZZ')
        return w.s([n], 'ex', '( %s -> ( ( Re ` z ) = %s -> -. ( Re ` z ) e. ZZ ) )' % (Az, X))
    j1 = reX(AL, s([nh], 'simpld', '-. %s e. ZZ' % AL))
    j2 = reX(BR, s([nh], 'simprd', '-. %s e. ZZ' % BR))
    jo = w.s([j1, j2], 'jaod', '( %s -> ( ( ( Re ` z ) = %s \\/ ( Re ` z ) = %s ) -> -. ( Re ` z ) e. ZZ ) )' % (Az, AL, BR))
    Ai = '( %s /\\ 1 <_ %s )' % (Az, AIz('z'))
    j3 = w.s([imne0(w, Ai, lift(w, zc, Ai), w.s([], 'simpr', '( %s -> 1 <_ %s )' % (Ai, AIz('z'))))], 'ex', '( %s -> ( 1 <_ %s -> ( Im ` z ) =/= 0 ) )' % (Az, AIz('z')))
    om = w.s([jo, j3], 'orim12d', '( %s -> ( %s -> ( -. ( Re ` z ) e. ZZ \\/ ( Im ` z ) =/= 0 ) ) )' % (Az, DJ))
    zd = t([zc, t([dj, om], 'mpd', '( -. ( Re ` z ) e. ZZ \\/ ( Im ` z ) =/= 0 )'), w.inst('z6mndg')], 'syl2anc', 'z e. %s' % DG)
    sd = s([w.s([zd], 'ex', '( ( %s /\\ z e. CC ) -> ( ( %s /\\ %s ) -> z e. %s ) )' % (A, RNG, DJ, DG))], 'ralrimiva', SD)
    # STRIPM
    Am = '( ( %s /\\ z e. CC ) /\\ ( %s /\\ 1 <_ %s ) )' % (A, RNG, AIz('z'))
    t = mkst(w, Am)
    zc = w.s([], 'simplr', '( %s -> z e. CC )' % Am)
    ge = w.s([], 'simprr', '( %s -> 1 <_ %s )' % (Am, AIz('z')))
    zdg = dgim(w, Am, zc, ge)
    gv, V = gyval(w, Am, 'z', zdg)
    gl = t([t([lift(w, yrp, Am), lift(w, kn, Am)], 'jca', '( Y e. RR+ /\\ K e. NN0 )'), t([zc, w.s([], 'simpr', '( %s -> ( %s /\\ 1 <_ %s ) )' % (Am, RNG, AIz('z')))], 'jca',
                                                                                              '( z e. CC /\\ ( %s /\\ 1 <_ %s ) )' % (RNG, AIz('z'))), w.inst('z6gyl')], 'syl2anc',
           '( abs ` %s ) <_ ( %s x. %s )' % (V, M0, E4(AIz('z'))))
    bm = t([gv, gl], 'eqbrtrd', '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (GYM, M0, E4(AIz('z'))))
    sm = s([w.s([bm], 'ex', '( ( %s /\\ z e. CC ) -> ( ( %s /\\ 1 <_ %s ) -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )' % (A, RNG, AIz('z'), GYM, M0, E4(AIz('z'))))],
           'ralrimiva', SM)
    # the rectangle integrals
    At = '( %s /\\ t e. RR+ )' % A
    RI = '( %s rectint <. ( %s + ( _i x. -u t ) ) , ( %s + ( _i x. t ) ) >. )' % (GYM, AL, BR)
    rt = w.s([w.s([], 'id', '( %s -> %s )' % (At, At)), w.inst('z6mrect')], 'syl', '( %s -> %s = %s )' % (At, RI, KR))
    rall = s([w.s([rt], 'a1d', '( %s -> ( 1 <_ t -> %s = %s ) )' % (At, RI, KR))], 'ralrimiva', 'A. t e. RR+ ( 1 <_ t -> %s = %s )' % (RI, KR))
    yc = s([yrp], 'rpcnd', 'Y e. CC')
    fn = s([kn, w.inst('faccl')], 'syl', '( ! ` K ) e. NN')
    krc = s([tpic(w, A), s([s([s([yc], 'negcld', '-u Y e. CC'), kn], 'expcld', '( -u Y ^ K ) e. CC'), s([fn], 'nncnd', '( ! ` K ) e. CC'), s([fn], 'nnne0d', '( ! ` K ) =/= 0')],
                                  'divcld', '( ( -u Y ^ K ) / ( ! ` K ) ) e. CC')], 'mulcld', '%s e. CC' % KR)
    m0 = cl.mem(M0, 'RR')
    HS = split_imp(sub(STATEMENTS['z6shift'], {'A': AL, 'B': BR, 'G': GYM, 'D': DG, 'M': M0, 'Y': '1', 'K': KR}))[0]
    h = s([ab, s([s([gyc, sd], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s )' % (GYM, DG, SD)), s([s([m0, a1c(w, A, '1rp', '1 e. RR+')], 'jca', '( %s e. RR /\\ 1 e. RR+ )' % M0), sm], 'jca',
                                                                                                   '( ( %s e. RR /\\ 1 e. RR+ ) /\\ %s )' % (M0, SM))], 'jca',
                  '( ( %s e. ( %s -cn-> CC ) /\\ %s ) /\\ ( ( %s e. RR /\\ 1 e. RR+ ) /\\ %s ) )' % (GYM, DG, SD, M0, SM)),
           s([krc, rall], 'jca', '( %s e. CC /\\ A. t e. RR+ ( 1 <_ t -> %s = %s ) )' % (KR, RI, KR))], '3jca', HS)
    w.qed([h, w.inst('z6shift')], 'syl', STATEMENTS['z6mstep'])
    return w


# ---------------------------------------------------------------- z6mvlr
def z6mvlr():
    w = W('z6mvlr', 'The Mellin line integrals converge on ` Re w = C ` , ` 1 / 2 <_ C <_ 3 ` ( ~ z6mgyvc with the majorant ~ z6gyr ).')
    A = split_imp(STATEMENTS['z6mvlr'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A)
    cr = w.s([], 'simprl', '( %s -> C e. RR )' % A)
    lo = w.s([], 'simprrl', '( %s -> %s <_ C )' % (A, H)); hi = w.s([], 'simprrr', '( %s -> C <_ 3 )' % A)
    cl = Closure(w, A, {'C': ('RR', cr)})
    cgt = linarith(w, A, [lo], '0 < C', closure=cl)
    Av = '( %s /\\ v e. RR )' % A
    t = mkst(w, Av)
    vr = w.s([], 'simpr', '( %s -> v e. RR )' % Av)
    Z = '( C + ( _i x. v ) )'
    zc = t([t([lift(w, cr, Av)], 'recnd', 'C e. CC'), t([a1c(w, Av, 'ax-icn', '_i e. CC'), t([vr], 'recnd', 'v e. CC')], 'mulcld', '( _i x. v ) e. CC')], 'addcld', '%s e. CC' % Z)
    re = t([lift(w, cr, Av), vr], 'crred', '( Re ` %s ) = C' % Z)
    im = t([lift(w, cr, Av), vr], 'crimd', '( Im ` %s ) = v' % Z)
    zdg = t([zc, t([lift(w, cgt, Av), re], 'breqtrrd', '0 < ( Re ` %s )' % Z), w.inst('zrenn')], 'syl2anc', '%s e. %s' % (Z, DG))
    ald = s([zdg], 'ralrimiva', 'A. v e. RR %s e. %s' % (Z, DG))
    gr = t([lift(w, yrp, Av), t([zc, t([t([lift(w, lo, Av), re], 'breqtrrd', '%s <_ ( Re ` %s )' % (H, Z)), t([re, lift(w, hi, Av)], 'eqbrtrd', '( Re ` %s ) <_ 3' % Z)], 'jca',
                                        '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (H, Z, Z))], 'jca', '( %s e. CC /\\ ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) )' % (Z, H, Z, Z)),
            w.inst('z6gyr')], 'syl2anc', '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s )' % (Z, Z, M1, E4(AIz(Z))))
    gr2 = t([gr, e4eq(w, Av, t([im], 'fveq2d', '%s = ( abs ` v )' % AIz(Z)), AIz(Z), '( abs ` v )', M1)], 'breqtrd',
            '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s )' % (Z, Z, M1, E4('( abs ` v )')))
    BV = '( 1 <_ ( abs ` v ) -> ( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s ) )' % (Z, Z, M1, E4('( abs ` v )'))
    alb = s([w.s([gr2], 'a1d', '( %s -> %s )' % (Av, BV))], 'ralrimiva', 'A. v e. RR %s' % BV)
    clm = Closure(w, A, {'Y': ('RR+', yrp)})
    HV = split_imp(sub(STATEMENTS['z6mgyvc'], {'M': M1, 'R': '1'}))[0]
    CV = split_imp(sub(STATEMENTS['z6mgyvc'], {'M': M1, 'R': '1'}))[1]
    h = s([s([s([yrp, cr], 'jca', '( Y e. RR+ /\\ C e. RR )'), ald], 'jca', '( ( Y e. RR+ /\\ C e. RR ) /\\ A. v e. RR %s e. %s )' % (Z, DG)),
           s([s([clm.mem(M1, 'RR'), a1c(w, A, '1rp', '1 e. RR+')], 'jca', '( %s e. RR /\\ 1 e. RR+ )' % M1), alb], 'jca', '( ( %s e. RR /\\ 1 e. RR+ ) /\\ A. v e. RR %s )' % (M1, BV))],
          'jca', HV)
    c = s([h, w.inst('z6mgyvc')], 'syl', CV)
    w.qed([c], 'simpld', STATEMENTS['z6mvlr'])
    return w


# ---------------------------------------------------------------- z6mvll
def lineleft(w, A, yrp, kn, kr, v):
    """steps under A for the line Re = AL: ( A -> A. v e. RR ( AL + i v ) e. DG ) and ( A -> A. v e. RR ( 1 <_ |v| -> bound M0 ) )"""
    s = mkst(w, A)
    Av = '( %s /\\ %s e. RR )' % (A, v)
    t = mkst(w, Av)
    vr = w.s([], 'simpr', '( %s -> %s e. RR )' % (Av, v))
    Z = '( %s + ( _i x. %s ) )' % (AL, v)
    cl = Closure(w, Av, {'K': ('RR', lift(w, kr, Av))})
    alr = cl.mem(AL, 'RR')
    zc = t([t([alr], 'recnd', '%s e. CC' % AL), t([a1c(w, Av, 'ax-icn', '_i e. CC'), t([vr], 'recnd', '%s e. CC' % v)], 'mulcld', '( _i x. %s ) e. CC' % v)], 'addcld', '%s e. CC' % Z)
    re = t([alr, vr], 'crred', '( Re ` %s ) = %s' % (Z, AL))
    im = t([alr, vr], 'crimd', '( Im ` %s ) = %s' % (Z, v))
    nz = t([t([lift(w, kn, Av), w.inst('z6mnhz')], 'syl', '( -. %s e. ZZ /\\ -. %s e. ZZ )' % (AL, BR))], 'simpld', '-. %s e. ZZ' % AL)
    zdg = dgre(w, Av, zc, re, nz, Z)
    ald = s([zdg], 'ralrimiva', 'A. %s e. RR %s e. %s' % (v, Z, DG))
    Ab = '( %s /\\ 1 <_ ( abs ` %s ) )' % (Av, v)
    b = mkst(w, Ab)
    aim = b([lift(w, im, Ab)], 'fveq2d', '%s = ( abs ` %s )' % (AIz(Z), v))
    ge = b([w.s([], 'simpr', '( %s -> 1 <_ ( abs ` %s ) )' % (Ab, v)), aim], 'breqtrrd', '1 <_ %s' % AIz(Z))
    lo = b([b([lift(w, alr, Ab)], 'leidd', '%s <_ %s' % (AL, AL)), lift(w, re, Ab)], 'breqtrrd', '%s <_ ( Re ` %s )' % (AL, Z))
    hi = b([lift(w, re, Ab), linarith(w, Ab, [], '%s <_ %s' % (AL, BR), closure=Closure(w, Ab, {'K': ('RR', lift(w, kr, Ab))}))], 'eqbrtrd', '( Re ` %s ) <_ %s' % (Z, BR))
    COND = '( ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) /\\ 1 <_ %s )' % (AL, Z, Z, BR, AIz(Z))
    gl = b([b([lift(w, yrp, Ab), lift(w, kn, Ab)], 'jca', '( Y e. RR+ /\\ K e. NN0 )'), b([lift(w, zc, Ab), b([b([lo, hi], 'jca', '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s )' % (AL, Z, Z, BR)), ge],
                                                                                                  'jca', COND)], 'jca', '( %s e. CC /\\ %s )' % (Z, COND)), w.inst('z6gyl')], 'syl2anc',
           '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s )' % (Z, Z, M0, E4(AIz(Z))))
    gl2 = b([gl, e4eq(w, Ab, aim, AIz(Z), '( abs ` %s )' % v, M0)], 'breqtrd', '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s )' % (Z, Z, M0, E4('( abs ` %s )' % v)))
    BV = '( 1 <_ ( abs ` %s ) -> ( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. %s ) )' % (v, Z, Z, M0, E4('( abs ` %s )' % v))
    alb = s([w.s([gl2], 'ex', '( %s -> %s )' % (Av, BV))], 'ralrimiva', 'A. %s e. RR %s' % (v, BV))
    return ald, alb, Z, BV


def z6mvll():
    w = W('z6mvll', 'The Mellin line integrals converge on ` Re w = -u K - 1 / 2 ` ( ~ z6mgyvc with the strip majorant ~ z6gyl ).')
    A = split_imp(STATEMENTS['z6mvll'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A)
    kr = s([kn], 'nn0red', 'K e. RR')
    ald, alb, Z, BV = lineleft(w, A, yrp, kn, kr, 'v')
    cl = Closure(w, A, {'K': ('RR', kr), 'Y': ('RR+', yrp)})
    S = sub(STATEMENTS['z6mgyvc'], {'M': M0, 'R': '1', 'C': AL})
    HV, CV = split_imp(S)
    h = s([s([s([yrp, cl.mem(AL, 'RR')], 'jca', '( Y e. RR+ /\\ %s e. RR )' % AL), ald], 'jca', '( ( Y e. RR+ /\\ %s e. RR ) /\\ A. v e. RR %s e. %s )' % (AL, Z, DG)),
           s([s([cl.mem(M0, 'RR'), a1c(w, A, '1rp', '1 e. RR+')], 'jca', '( %s e. RR /\\ 1 e. RR+ )' % M0), alb], 'jca', '( ( %s e. RR /\\ 1 e. RR+ ) /\\ A. v e. RR %s )' % (M0, BV))],
          'jca', HV)
    c = s([h, w.inst('z6mgyvc')], 'syl', CV)
    w.qed([c], 'simpld', STATEMENTS['z6mvll'])
    return w


# ---------------------------------------------------------------- z6mright
def z6mright():
    w = W('z6mright', 'The Mellin line moves freely on ` 1 / 2 <_ Re w <_ 3 ` : no pole ( ~ z6shift with ~ rectintgour , the majorant ~ z6gyr ).')
    A = split_imp(STATEMENTS['z6mright'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A)
    cr = w.s([], 'simprl', '( %s -> C e. RR )' % A)
    lo = w.s([], 'simprrl', '( %s -> %s <_ C )' % (A, H)); hi = w.s([], 'simprrr', '( %s -> C <_ 3 )' % A)
    # C = 1 / 2
    At = '( %s /\\ C = %s )' % (A, H)
    ceq = w.s([], 'simpr', '( %s -> C = %s )' % (At, H))
    tt, new = w.congr(VL(GYM, 'C'), {'C': H}, At, {'C': ceq})
    assert new == VL(GYM, H)
    # C > 1 / 2
    Af = '( %s /\\ -. C = %s )' % (A, H)
    f = mkst(w, Af)
    crf = lift(w, cr, Af)
    clf = Closure(w, Af, {'C': ('RR', crf), 'Y': ('RR+', lift(w, yrp, Af))})
    hr = clf.mem(H, 'RR')
    lt = f([f([lift(w, lo, Af), f([w.s([], 'simpr', '( %s -> -. C = %s )' % (Af, H))], 'neqned', 'C =/= %s' % H)], 'jca', '( %s <_ C /\\ C =/= %s )' % (H, H)),
            f([hr, crf, w.inst('ltlen')], 'syl2anc', '( %s < C <-> ( %s <_ C /\\ C =/= %s ) )' % (H, H, H))], 'mpbird', '%s < C' % H)
    ab = f([f([hr, crf], 'jca', '( %s e. RR /\\ C e. RR )' % H), lt], 'jca', '( ( %s e. RR /\\ C e. RR ) /\\ %s < C )' % (H, H))
    gyh = f([lift(w, yrp, Af), w.inst('z6gyhol')], 'syl', HOLG(GYM, DG))
    gyc = f([gyh], 'simpld', '%s e. ( %s -cn-> CC )' % (GYM, DG))
    SD = sub(STRIPD, {'A': H, 'B': 'C', 'Y': '1', 'D': DG})
    SM = sub(STRIPM, {'A': H, 'B': 'C', 'Y': '1', 'G': GYM, 'M': M1})
    RNG = '( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ C )' % H
    DJ = '( ( ( Re ` z ) = %s \\/ ( Re ` z ) = C ) \\/ 1 <_ %s )' % (H, AIz('z'))
    Az = '( ( %s /\\ z e. CC ) /\\ %s )' % (Af, RNG)
    t = mkst(w, Az)
    zc = w.s([], 'simplr', '( %s -> z e. CC )' % Az)
    rz = t([zc], 'recld', '( Re ` z ) e. RR')
    zlo = w.s([], 'simprl', '( %s -> %s <_ ( Re ` z ) )' % (Az, H)); zhi = w.s([], 'simprr', '( %s -> ( Re ` z ) <_ C )' % Az)
    clz = Closure(w, Az, {'( Re ` z )': ('RR', rz), 'C': ('RR', lift(w, crf, Az))})
    zdg = t([zc, linarith(w, Az, [zlo], '0 < ( Re ` z )', closure=clz), w.inst('zrenn')], 'syl2anc', 'z e. %s' % DG)
    sd = f([w.s([w.s([zdg], 'adantrr', '( ( ( %s /\\ z e. CC ) /\\ ( %s /\\ %s ) ) -> z e. %s )' % (Af, RNG, DJ, DG))], 'ex',
                '( ( %s /\\ z e. CC ) -> ( ( %s /\\ %s ) -> z e. %s ) )' % (Af, RNG, DJ, DG))], 'ralrimiva', SD)
    gv, V = gyval(w, Az, 'z', zdg)
    z3 = linarith(w, Az, [zhi, lift(w, hi, Az)], '( Re ` z ) <_ 3', closure=clz)
    gr = t([lift(w, yrp, Az), t([zc, t([zlo, z3], 'jca', '( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 )' % H)], 'jca', '( z e. CC /\\ ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) )' % H),
            w.inst('z6gyr')], 'syl2anc', '( abs ` %s ) <_ ( %s x. %s )' % (V, M1, E4(AIz('z'))))
    bm = t([gv, gr], 'eqbrtrd', '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (GYM, M1, E4(AIz('z'))))
    BM = '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (GYM, M1, E4(AIz('z')))
    sm = f([w.s([w.s([bm], 'adantrr', '( ( ( %s /\\ z e. CC ) /\\ ( %s /\\ 1 <_ %s ) ) -> %s )' % (Af, RNG, AIz('z'), BM))], 'ex',
                '( ( %s /\\ z e. CC ) -> ( ( %s /\\ 1 <_ %s ) -> %s ) )' % (Af, RNG, AIz('z'), BM))], 'ralrimiva', SM)
    # rectangles: Goursat
    Atr = '( %s /\\ t e. RR+ )' % Af
    r = mkst(w, Atr)
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % Atr)
    tr = r([trp], 'rpred', 't e. RR')
    CA = '( %s + ( _i x. -u t ) )' % H; CB = '( C + ( _i x. t ) )'
    RT = '( %s crect %s )' % (CA, CB)
    hr2 = lift(w, hr, Atr); cr2 = lift(w, crf, Atr)
    ntr = r([tr], 'renegcld', '-u t e. RR')
    ic = a1c(w, Atr, 'ax-icn', '_i e. CC')
    cac = r([r([hr2], 'recnd', '%s e. CC' % H), r([ic, r([ntr], 'recnd', '-u t e. CC')], 'mulcld', '( _i x. -u t ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = r([r([cr2], 'recnd', 'C e. CC'), r([ic, r([tr], 'recnd', 't e. CC')], 'mulcld', '( _i x. t ) e. CC')], 'addcld', '%s e. CC' % CB)
    reA = r([hr2, ntr], 'crred', '( Re ` %s ) = %s' % (CA, H)); reB = r([cr2, tr], 'crred', '( Re ` %s ) = C' % CB)
    imA = r([hr2, ntr], 'crimd', '( Im ` %s ) = -u t' % CA); imB = r([cr2, tr], 'crimd', '( Im ` %s ) = t' % CB)
    clt = Closure(w, Atr, {'t': ('RR', tr), 'C': ('RR', cr2)})
    rle = r([r([lift(w, lt, Atr)], 'ltled', '%s <_ C' % H), reA, reB], '3brtr4d', '( Re ` %s ) <_ ( Re ` %s )' % (CA, CB))
    ile = r([linarith(w, Atr, [r([trp], 'rpge0d', '0 <_ t')], '-u t <_ t', closure=clt), imA, imB], '3brtr4d', '( Im ` %s ) <_ ( Im ` %s )' % (CA, CB))
    Azr = '( %s /\\ z e. %s )' % (Atr, RT)
    u = mkst(w, Azr)
    ec = u([lift(w, cac, Azr), lift(w, cbc, Azr), w.inst('elcrect')], 'syl2anc',
           '( z e. %s <-> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (RT, CA, CB, CA, CB))
    z3_ = u([w.s([], 'simpr', '( %s -> z e. %s )' % (Azr, RT)), ec], 'mpbid', '( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (CA, CB, CA, CB))
    zcc = u([z3_], 'simp1d', 'z e. CC')
    riv = u([lift(w, reA, Azr), lift(w, reB, Azr)], 'oveq12d', '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( %s [,] C )' % (CA, CB, H))
    ri = u([u([z3_], 'simp2d', '( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (CA, CB)), riv], 'eleqtrd', '( Re ` z ) e. ( %s [,] C )' % H)
    r3 = u([ri, u([lift(w, hr, Azr), lift(w, crf, Azr), w.inst('elicc2')], 'syl2anc', '( ( Re ` z ) e. ( %s [,] C ) <-> ( ( Re ` z ) e. RR /\\ %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ C ) )' % (H, H))],
           'mpbid', '( ( Re ` z ) e. RR /\\ %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ C )' % H)
    clr = Closure(w, Azr, {'( Re ` z )': ('RR', u([r3], 'simp1d', '( Re ` z ) e. RR'))})
    zdg2 = u([zcc, linarith(w, Azr, [u([r3], 'simp2d', '%s <_ ( Re ` z )' % H)], '0 < ( Re ` z )', closure=clr), w.inst('zrenn')], 'syl2anc', 'z e. %s' % DG)
    rdg = r([w.s([zdg2], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (Atr, RT, DG))], 'ssrdv', '%s C_ %s' % (RT, DG))
    rdom = r([rdg, r([lift(w, gyh, Atr)], 'simprd', '%s C_ dom ( CC _D %s )' % (DG, GYM))], 'sstrd', '%s C_ dom ( CC _D %s )' % (RT, GYM))
    RI = '( %s rectint <. %s , %s >. )' % (GYM, CA, CB)
    gou = r([r([r([cac, cbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (CA, CB)), r([rle, ile], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (CA, CB, CA, CB)),
                r([lift(w, gyc, Atr), rdom], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (GYM, DG, RT, GYM))], '3jca',
               '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )'
               % (CA, CB, CA, CB, CA, CB, GYM, DG, RT, GYM)), w.inst('rectintgour')], 'syl', '%s = 0' % RI)
    rall = f([w.s([gou], 'a1d', '( %s -> ( 1 <_ t -> %s = 0 ) )' % (Atr, RI))], 'ralrimiva', 'A. t e. RR+ ( 1 <_ t -> %s = 0 )' % RI)
    HS, CS = split_imp(sub(STATEMENTS['z6shift'], {'A': H, 'B': 'C', 'G': GYM, 'D': DG, 'M': M1, 'Y': '1', 'K': '0'}))
    h = f([ab, f([f([gyc, sd], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s )' % (GYM, DG, SD)), f([f([clf.mem(M1, 'RR'), a1c(w, Af, '1rp', '1 e. RR+')], 'jca', '( %s e. RR /\\ 1 e. RR+ )' % M1), sm],
                                                                                                 'jca', '( ( %s e. RR /\\ 1 e. RR+ ) /\\ %s )' % (M1, SM))], 'jca',
                  '( ( %s e. ( %s -cn-> CC ) /\\ %s ) /\\ ( ( %s e. RR /\\ 1 e. RR+ ) /\\ %s ) )' % (GYM, DG, SD, M1, SM)),
           f([a1c(w, Af, '0cn', '0 e. CC'), rall], 'jca', '( 0 e. CC /\\ A. t e. RR+ ( 1 <_ t -> %s = 0 ) )' % RI)], '3jca', HS)
    sh = f([h, w.inst('z6shift')], 'syl', CS)
    vc = f([f([lift(w, w.s([], 'id', '( %s -> %s )' % (A, A)), Af), w.inst('z6mvlr')], 'syl', '%s ~~>r %s' % (VLF(GYM, 'C'), VL(GYM, 'C'))), w.inst('rlimcl')], 'syl',
           '%s e. CC' % VL(GYM, 'C'))
    AH = '( Y e. RR+ /\\ ( %s e. RR /\\ ( %s <_ %s /\\ %s <_ 3 ) ) )' % (H, H, H, H)
    hh = f([lift(w, yrp, Af), f([hr, f([f([hr], 'leidd', '%s <_ %s' % (H, H)), clf.mem(H, 'RR') and linarith(w, Af, [], '%s <_ 3' % H, closure=clf)], 'jca',
                                       '( %s <_ %s /\\ %s <_ 3 )' % (H, H, H))], 'jca', '( %s e. RR /\\ ( %s <_ %s /\\ %s <_ 3 ) )' % (H, H, H, H))], 'jca', AH)
    vh = f([f([hh, w.inst('z6mvlr')], 'syl', '%s ~~>r %s' % (VLF(GYM, H), VL(GYM, H))), w.inst('rlimcl')], 'syl', '%s e. CC' % VL(GYM, H))
    ff = f([vc, vh, sh], 'subeq0d', '%s = %s' % (VL(GYM, 'C'), VL(GYM, H)))
    w.qed([tt, ff], 'pm2.61dan', STATEMENTS['z6mright'])
    return w


# ---------------------------------------------------------------- z6mlt
def z6mlt():
    w = W('z6mlt', 'The truncated left line integral: ` | LI ( -u K - 1 / 2 , T ) | <_ ( 2 Y ^ ( K + 1 / 2 ) / K ! ) KG ` '
          '( ~ z6lvert , ~ itgabs , ~ z6gyline , the moment ~ z6gmom at ` 1 / 2 ` with ` ( 1 + | u | ) ^ 2 >_ 1 ` ).')
    A = split_imp(STATEMENTS['z6mlt'])[0]
    s = mkst(w, A)
    A0 = '( Y e. RR+ /\\ K e. NN0 )'
    yrp = w.s([], 'simpll', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % A); trp = w.s([], 'simpr', '( %s -> T e. RR+ )' % A)
    kr = s([kn], 'nn0red', 'K e. RR')
    ald, _, Zu, _ = lineleft(w, A, yrp, kn, kr, 'u')
    cl = Closure(w, A, {'K': ('RR', kr), 'Y': ('RR+', yrp)})
    cl.leaf('( ! ` K )', 'NN', s([kn, w.inst('faccl')], 'syl', '( ! ` K ) e. NN'))
    alr = cl.mem(AL, 'RR')
    seg = s([s([s([alr, trp], 'jca', '( %s e. RR /\\ T e. RR+ )' % AL), ald], 'jca', '( ( %s e. RR /\\ T e. RR+ ) /\\ A. u e. RR %s e. %s )' % (AL, Zu, DG)), w.inst('z6segd')], 'syl',
            '( ( %s + ( _i x. -u T ) ) cseg ( %s + ( _i x. T ) ) ) C_ %s' % (AL, AL, DG))
    gyc = s([s([yrp, w.inst('z6gyhol')], 'syl', HOLG(GYM, DG))], 'simpld', '%s e. ( %s -cn-> CC )' % (GYM, DG))
    IO = '( -u T (,) T )'
    FU = '( %s ` %s )' % (GYM, Zu)
    ITG = 'S. %s %s _d u' % (IO, FU)
    LIT = LI(GYM, AL, 'T')
    lv = s([s([s([alr, trp], 'jca', '( %s e. RR /\\ T e. RR+ )' % AL), s([gyc, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( ( %s + ( _i x. -u T ) ) cseg ( %s + ( _i x. T ) ) ) C_ %s )' % (GYM, DG, AL, AL, DG))],
              'jca', '( ( %s e. RR /\\ T e. RR+ ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( ( %s + ( _i x. -u T ) ) cseg ( %s + ( _i x. T ) ) ) C_ %s ) )' % (AL, GYM, DG, AL, AL, DG)),
            w.inst('z6lvert')], 'syl', '( ( u e. %s |-> %s ) e. L^1 /\\ %s = ( _i x. %s ) )' % (IO, FU, LIT, ITG))
    ibl = s([lv], 'simpld', '( u e. %s |-> %s ) e. L^1' % (IO, FU))
    leq = s([lv], 'simprd', '%s = ( _i x. %s )' % (LIT, ITG))
    Au = '( %s /\\ u e. %s )' % (A, IO)
    t = mkst(w, Au)
    ur = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au, IO)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % Au)
    zdg = w.s([ald], 'r19.21bi', '( ( %s /\\ u e. RR ) -> %s e. %s )' % (A, Zu, DG))
    zdgu = w.s([w.s([], 'simpl', '( %s -> %s )' % (Au, A)), ur, zdg], 'syl2anc', '( %s -> %s e. %s )' % (Au, Zu, DG))
    fuc = t([w.s([lift(w, gyc, Au), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Au, GYM, DG)), zdgu], 'ffvelcdmd', '%s e. CC' % FU)
    gv, V = gyval(w, Au, Zu, zdgu)
    c = '( ( 2 x. ( Y ^c ( K + ( 1 / 2 ) ) ) ) / ( ! ` K ) )'
    HL = '( ( 1 / 2 ) + ( _i x. u ) )'
    g = '( abs ` ( _G ` %s ) )' % HL
    Q = '( ( 1 + ( abs ` u ) ) ^ 2 )'
    gl = t([t([t([lift(w, yrp, Au), lift(w, kn, Au)], 'jca', '( Y e. RR+ /\\ K e. NN0 )'), ur], 'jca', '( ( Y e. RR+ /\\ K e. NN0 ) /\\ u e. RR )'), w.inst('z6gyline')], 'syl',
           '( abs ` %s ) <_ ( %s x. %s )' % (V, c, g))
    clu = Closure(w, Au, {'K': ('RR', lift(w, kr, Au)), 'Y': ('RR+', lift(w, yrp, Au)), 'u': ('RR', ur)})
    fn = t([lift(w, kn, Au), w.inst('faccl')], 'syl', '( ! ` K ) e. NN')
    clu.leaf('( ! ` K )', 'NN', fn)
    hc = t([a1c(w, Au, 'halfcn', '( 1 / 2 ) e. CC'), t([a1c(w, Au, 'ax-icn', '_i e. CC'), t([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % HL)
    hre = t([a1c(w, Au, 'halfre', '( 1 / 2 ) e. RR'), ur], 'crred', '( Re ` %s ) = ( 1 / 2 )' % HL)
    hdg = t([hc, t([a1c(w, Au, 'halfgt0', '0 < ( 1 / 2 )'), hre], 'breqtrrd', '0 < ( Re ` %s )' % HL), w.inst('zrenn')], 'syl2anc', '%s e. %s' % (HL, DG))
    gr = t([t([hdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % HL)], 'abscld', '%s e. RR' % g)
    clu.leaf(g, 'RR', gr)
    qr = clu.mem(Q, 'RR')
    au = t([t([ur], 'recnd', 'u e. CC')], 'absge0d', '0 <_ ( abs ` u )')
    o1 = linarith(w, Au, [au], '1 <_ ( 1 + ( abs ` u ) )', closure=clu)
    q1 = t([clu.mem('( 1 + ( abs ` u ) )', 'RR'), a1c(w, Au, '2nn0', '2 e. NN0'), o1, w.inst('expge1')], 'syl3anc', '1 <_ %s' % Q)
    gq = t([t([a1c(w, Au, '1re', '1 e. RR'), qr, gr, t([t([hdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % HL)], 'absge0d', '0 <_ %s' % g), q1], 'lemul2ad',
              '( %s x. 1 ) <_ ( %s x. %s )' % (g, g, Q)), t([t([gr], 'recnd', '%s e. CC' % g)], 'mulridd', '( %s x. 1 ) = %s' % (g, g))], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (g, g, Q))
    cr_ = clu.mem(c, 'RR')
    cg = t([gr, clu.mem('( %s x. %s )' % (g, Q), 'RR'), cr_, clu.ge0(c), gq], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (c, g, c, g, Q))
    AFU = '( abs ` %s )' % FU
    b1 = t([gv, gl], 'eqbrtrd', '%s <_ ( %s x. %s )' % (AFU, c, g))
    afr = t([fuc], 'abscld', '%s e. RR' % AFU)
    RHS = '( %s x. ( %s x. %s ) )' % (c, g, Q)
    pb = t([afr, clu.mem('( %s x. %s )' % (c, g), 'RR'), clu.mem(RHS, 'RR'), b1, cg], 'letrd', '%s <_ %s' % (AFU, RHS))
    # the integrals
    mom = s([s([s([a1c(w, A, 'halfre', '( 1 / 2 ) e. RR'), w.s([num.le_lit(w, '( 1 / ; ; 1 0 0 )', '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / ; ; 1 0 0 ) <_ ( 1 / 2 ) )' % A),
                        w.s([num.le_lit(w, '( 1 / 2 )', '3')], 'a1i', '( %s -> ( 1 / 2 ) <_ 3 )' % A)], '3jca', '( ( 1 / 2 ) e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 3 )'), trp],
                 'jca', '( ( ( 1 / 2 ) e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 3 ) /\\ T e. RR+ )'), w.inst('z6gmom')], 'syl',
            '( %s e. L^1 /\\ %s <_ %s )' % (MOMF(H), MOM(H), KG))
    mibl = s([mom], 'simpld', '%s e. L^1' % MOMF(H)); mle = s([mom], 'simprd', '%s <_ %s' % (MOM(H), KG))
    GQ = '( %s x. %s )' % (g, Q)
    gqc = t([clu.mem(GQ, 'RR')], 'recnd', '%s e. CC' % GQ)
    cc_ = cl.mem(c, 'RR')
    ib2 = s([s([cc_], 'recnd', '%s e. CC' % c), gqc, mibl], 'iblmulc2', '( u e. %s |-> ( %s x. %s ) ) e. L^1' % (IO, c, GQ))
    ib1 = s([fuc, ibl], 'iblabs', '( u e. %s |-> %s ) e. L^1' % (IO, AFU))
    ia = s([fuc, ibl], 'itgabs', '( abs ` %s ) <_ S. %s %s _d u' % (ITG, IO, AFU))
    il = s([ib1, ib2, afr, clu.mem(RHS, 'RR'), pb], 'itgle', 'S. %s %s _d u <_ S. %s %s _d u' % (IO, AFU, IO, RHS))
    im = s([s([cc_], 'recnd', '%s e. CC' % c), gqc, mibl], 'itgmulc2', '( %s x. %s ) = S. %s %s _d u' % (c, MOM(H), IO, RHS))
    # MOM real
    kgr = cl.mem(KG, 'RR')
    ml = s([momr_(w, A, mibl, clu, GQ, IO), kgr, cc_, cl.ge0(c), mle], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (c, MOM(H), c, KG))
    itgabsr = s([s([fuc, ibl], 'itgcl', '%s e. CC' % ITG)], 'abscld', '( abs ` %s ) e. RR' % ITG)
    i1r = itgre(w, A, afr, ib1, 'S. %s %s _d u' % (IO, AFU))
    i2r = itgre(w, A, clu.mem(RHS, 'RR'), ib2, 'S. %s %s _d u' % (IO, RHS))
    ch1 = s([itgabsr, i1r, i2r, ia, il], 'letrd', '( abs ` %s ) <_ S. %s %s _d u' % (ITG, IO, RHS))
    ch2 = s([ch1, im], 'breqtrrd', '( abs ` %s ) <_ ( %s x. %s )' % (ITG, c, MOM(H)))
    ch3 = s([itgabsr, s([cc_, momr_(w, A, mibl, clu, GQ, IO)], 'remulcld', '( %s x. %s ) e. RR' % (c, MOM(H))), s([cc_, kgr], 'remulcld', '( %s x. %s ) e. RR' % (c, KG)), ch2, ml],
            'letrd', '( abs ` %s ) <_ ( %s x. %s )' % (ITG, c, KG))
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    ae = s([s([leq], 'fveq2d', '( abs ` %s ) = ( abs ` ( _i x. %s ) )' % (LIT, ITG)), s([ic, s([fuc, ibl], 'itgcl', '%s e. CC' % ITG)], 'absmuld', '( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (ITG, ITG))],
           'eqtrd', '( abs ` %s ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (LIT, ITG))
    ai = s([s([a1c(w, A, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) )' % (ITG, ITG)),
            s([s([itgabsr], 'recnd', '( abs ` %s ) e. CC' % ITG)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (ITG, ITG))], 'eqtrd',
           '( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s )' % (ITG, ITG))
    fin = s([s([ae, ai], 'eqtrd', '( abs ` %s ) = ( abs ` %s )' % (LIT, ITG)), ch3], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (LIT, c, KG))
    toqed(w, fin, 'z6mlt')
    return w


_MOMR = {}


def momr_(w, A, mibl, clu, GQ, IO):
    """( A -> MOM(1/2) e. RR ), memoized per worksheet"""
    key = (id(w), A)
    if key not in _MOMR:
        _MOMR[key] = itgre(w, A, clu.mem(GQ, 'RR'), mibl, MOM(H))
    return _MOMR[key]


def itgre(w, A, bodyr, ibl, ITG):
    """( A -> S. X B _d u e. RR ) from bodyr: ( ( A /\\ u e. X ) -> B e. RR ) and ibl"""
    return w.s([bodyr, ibl], 'itgrecl', '( %s -> %s e. RR )' % (A, ITG))


# ---------------------------------------------------------------- z6mleft
def z6mleft():
    w = W('z6mleft', 'The Mellin line integral on ` Re w = -u K - 1 / 2 ` is below ` ( 2 Y ^ ( K + 1 / 2 ) / K ! ) KG ` ( ~ z6mvll , ~ z6mlt , ~ z6rlimle ).')
    A = split_imp(STATEMENTS['z6mleft'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A)
    kr = s([kn], 'nn0red', 'K e. RR')
    cl = Closure(w, A, {'K': ('RR', kr), 'Y': ('RR+', yrp)})
    cl.leaf('( ! ` K )', 'NN', s([kn, w.inst('faccl')], 'syl', '( ! ` K ) e. NN'))
    B = '( ( ( 2 x. ( Y ^c ( K + ( 1 / 2 ) ) ) ) / ( ! ` K ) ) x. %s )' % KG
    lim = s([w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('z6mvll')], 'syl', '%s ~~>r %s' % (VLF(GYM, AL), VL(GYM, AL)))
    At = '( %s /\\ t e. RR+ )' % A
    lt = w.s([w.s([], 'id', '( %s -> %s )' % (At, At)), w.inst('z6mlt')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (At, LI(GYM, AL, 't'), B))
    ral = s([lt], 'ralrimiva', 'A. t e. RR+ ( abs ` %s ) <_ %s' % (LI(GYM, AL, 't'), B))
    w.qed([s([lim, s([cl.mem(B, 'RR'), ral], 'jca', '( %s e. RR /\\ A. t e. RR+ ( abs ` %s ) <_ %s )' % (B, LI(GYM, AL, 't'), B))], 'jca',
             '( %s ~~>r %s /\\ ( %s e. RR /\\ A. t e. RR+ ( abs ` %s ) <_ %s ) )' % (VLF(GYM, AL), VL(GYM, AL), B, LI(GYM, AL, 't'), B)), w.inst('z6rlimle')], 'syl', STATEMENTS['z6mleft'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6mstep, z6mvlr, z6mvll, z6mright, z6mlt, z6mleft]:
        if want(f.__name__):
            if run(f()):
                status(f.__name__)
            else:
                break
