"""Sortie v4b block 4: the remainder of the progression sieve.

crtres  ( ( D e. NN /\\ M e. NN /\\ ( D gcd M ) = 1 ) ->
            E. o e. ( 0 ..^ ( D x. M ) ) A. i e. ZZ
              ( ( ( i mod M ) = ( 1 mod M ) /\\ D || i ) <-> ( i mod ( D x. M ) ) = o ) )
crtcnt  the count of that class over ( 1 ... N ), within 1 of N / ( D x. M )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import CT, mkst
from cl import lift

ANT0 = '( D e. NN /\\ M e. NN /\\ ( D gcd M ) = 1 )'
DM = '( D x. M )'
B0 = '( D x. x )'
R = '( %s mod %s )' % (B0, DM)
MY = '( M x. y )'
EQ = '( D gcd M ) = ( %s + %s )' % (B0, MY)
AB = '( ( %s /\\ ( x e. ZZ /\\ y e. ZZ ) ) /\\ %s )' % (ANT0, EQ)
LHS = '( ( i mod M ) = ( 1 mod M ) /\\ D || i )'
RHS = lambda o: '( i mod %s ) = %s' % (DM, o)
ALLI = lambda o: 'A. i e. ZZ ( %s <-> %s )' % (LHS, RHS(o))
CONCL = 'E. o e. ( 0 ..^ %s ) %s' % (DM, ALLI('o'))


def crtres():
    w = W('crtres', 'For coprime D and M the two conditions i = 1 mod M and D || i single '
                    'out a single residue class modulo D x. M.')
    st = mkst(w, AB)
    a0 = st([], 'simpl', '( %s /\\ ( x e. ZZ /\\ y e. ZZ ) )' % ANT0)
    ph0 = st([a0], 'simpld', ANT0)
    dnn = st([ph0], 'simp1d', 'D e. NN')
    mnn = st([ph0], 'simp2d', 'M e. NN')
    gcd = st([ph0], 'simp3d', '( D gcd M ) = 1')
    xy = st([a0], 'simprd', '( x e. ZZ /\\ y e. ZZ )')
    xz = st([xy], 'simpld', 'x e. ZZ')
    yz = st([xy], 'simprd', 'y e. ZZ')
    eq = st([], 'simpr', EQ)
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    mz = st([mnn], 'nnzd', 'M e. ZZ')
    b0z = st([dz, xz, w.inst('zmulcl')], 'syl2anc', '%s e. ZZ' % B0)
    myz = st([mz, yz, w.inst('zmulcl')], 'syl2anc', '%s e. ZZ' % MY)
    dmn = st([dnn, mnn], 'nnmulcld', '%s e. NN' % DM)
    dmz = st([dmn], 'nnzd', '%s e. ZZ' % DM)
    rfzo = st([b0z, dmn, w.inst('zmodfzo')], 'syl2anc', '%s e. ( 0 ..^ %s )' % (R, DM))
    # M || ( 1 - ( D x. x ) )
    e1 = st([gcd, eq], 'eqtr3d', '1 = ( %s + %s )' % (B0, MY))
    e2 = st([e1], 'eqcomd', '( %s + %s ) = 1' % (B0, MY))
    onec = st([], '1cnd', '1 e. CC')
    b0c = st([b0z], 'zcnd', '%s e. CC' % B0)
    myc = st([myz], 'zcnd', '%s e. CC' % MY)
    sa = st([onec, b0c, myc, w.inst('subadd')], 'syl3anc',
            '( ( 1 - %s ) = %s <-> ( %s + %s ) = 1 )' % (B0, MY, B0, MY))
    e3 = st([sa, e2], 'mpbird', '( 1 - %s ) = %s' % (B0, MY))
    dmy = st([mz, yz, w.inst('dvdsmul1')], 'syl2anc', 'M || %s' % MY)
    m1b = st([dmy, e3], 'breqtrrd', 'M || ( 1 - %s )' % B0)
    onez = st([], '1zzd', '1 e. ZZ')
    md1 = st([mnn, onez, b0z, w.inst('moddvds')], 'syl3anc',
             '( ( 1 mod M ) = ( %s mod M ) <-> M || ( 1 - %s ) )' % (B0, B0))
    md1b = st([md1, m1b], 'mpbird', '( 1 mod M ) = ( %s mod M )' % B0)
    dxx = st([dz, xz, w.inst('dvdsmul1')], 'syl2anc', 'D || %s' % B0)
    ddm = st([dz, mz, w.inst('dvdsmul1')], 'syl2anc', 'D || %s' % DM)
    mdm = st([dz, mz, w.inst('dvdsmul2')], 'syl2anc', 'M || %s' % DM)
    # ---- the equivalence, under ( AB /\\ i e. ZZ ) -----------------------
    ABI = '( %s /\\ i e. ZZ )' % AB
    si = mkst(w, ABI)
    L = lambda s: lift(w, s, ABI)
    iz = si([], 'simpr', 'i e. ZZ')
    modb = si([L(dmn), iz, L(b0z), w.inst('moddvds')], 'syl3anc',
              '( ( i mod %s ) = %s <-> %s || ( i - %s ) )' % (DM, R, DM, B0))
    modm = si([L(mnn), iz, L(b0z), w.inst('moddvds')], 'syl3anc',
              '( ( i mod M ) = ( %s mod M ) <-> M || ( i - %s ) )' % (B0, B0))
    # forward
    AF = '( %s /\\ %s )' % (ABI, LHS)
    sf = mkst(w, AF)
    LF = lambda s: lift(w, s, AF)
    f1 = sf([], 'simprl', '( i mod M ) = ( 1 mod M )')
    f2 = sf([], 'simprr', 'D || i')
    fd = sf([LF(dz), LF(iz), LF(b0z), f2, LF(dxx)], 'dvds2subd', 'D || ( i - %s )' % B0)
    fm0 = sf([f1, LF(md1b)], 'eqtrd', '( i mod M ) = ( %s mod M )' % B0)
    fm = sf([LF(modm), fm0], 'mpbid', 'M || ( i - %s )' % B0)
    fsub = sf([LF(iz), LF(b0z), w.inst('zsubcl')], 'syl2anc', '( i - %s ) e. ZZ' % B0)
    fcop = sf([sf([LF(dz), LF(mz), fsub], '3jca',
                  '( D e. ZZ /\\ M e. ZZ /\\ ( i - %s ) e. ZZ )' % B0),
               LF(gcd), w.inst('coprmdvds2')], 'syl2anc',
              '( ( D || ( i - %s ) /\\ M || ( i - %s ) ) -> %s || ( i - %s ) )'
              % (B0, B0, DM, B0))
    fdm = sf([fcop, fd, fm], 'mp2and', '%s || ( i - %s )' % (DM, B0))
    fwd = sf([LF(modb), fdm], 'mpbird', RHS(R))
    # backward
    AG = '( %s /\\ %s )' % (ABI, RHS(R))
    sg = mkst(w, AG)
    LG = lambda s: lift(w, s, AG)
    g0 = sg([], 'simpr', RHS(R))
    gdm = sg([LG(modb), g0], 'mpbid', '%s || ( i - %s )' % (DM, B0))
    gsub = sg([LG(iz), LG(b0z), w.inst('zsubcl')], 'syl2anc', '( i - %s ) e. ZZ' % B0)
    gd = sg([sg([LG(dz), LG(dmz), gsub], '3jca',
               '( D e. ZZ /\\ %s e. ZZ /\\ ( i - %s ) e. ZZ )' % (DM, B0)),
             w.inst('dvdstr')], 'syl',
            '( ( D || %s /\\ %s || ( i - %s ) ) -> D || ( i - %s ) )' % (DM, DM, B0, B0))
    gd2 = sg([gd, LG(ddm), gdm], 'mp2and', 'D || ( i - %s )' % B0)
    gm = sg([sg([LG(mz), LG(dmz), gsub], '3jca',
               '( M e. ZZ /\\ %s e. ZZ /\\ ( i - %s ) e. ZZ )' % (DM, B0)),
             w.inst('dvdstr')], 'syl',
            '( ( M || %s /\\ %s || ( i - %s ) ) -> M || ( i - %s ) )' % (DM, DM, B0, B0))
    gm2 = sg([gm, LG(mdm), gdm], 'mp2and', 'M || ( i - %s )' % B0)
    gsub2 = sg([sg([LG(dz), LG(iz), LG(b0z)], '3jca',
                   '( D e. ZZ /\\ i e. ZZ /\\ %s e. ZZ )' % B0), gd2, w.inst('dvdssub2')],
               'syl2anc', '( D || i <-> D || %s )' % B0)
    gdi = sg([gsub2, LG(dxx)], 'mpbird', 'D || i')
    gmi0 = sg([LG(modm), gm2], 'mpbird', '( i mod M ) = ( %s mod M )' % B0)
    gmi = sg([gmi0, LG(md1b)], 'eqtr4d', '( i mod M ) = ( 1 mod M )')
    bwd = sg([gmi, gdi], 'jca', LHS)
    bic = si([fwd, bwd], 'impbida', '( %s <-> %s )' % (LHS, RHS(R)))
    alli = st([bic], 'ralrimiva', ALLI(R))
    # rspcev at o := R
    sb1 = w.s([], 'eqeq2d', '( o = %s -> ( %s <-> %s ) )' % (R, RHS('o'), RHS(R)))
    sb2 = w.s([sb1], 'bibi2d',
              '( o = %s -> ( ( %s <-> %s ) <-> ( %s <-> %s ) ) )' % (R, LHS, RHS('o'), LHS, RHS(R)))
    sb3 = w.s([sb2], 'ralbidv', '( o = %s -> ( %s <-> %s ) )' % (R, ALLI('o'), ALLI(R)))
    ex = st([rfzo, alli, w.s([sb3], 'rspcev',
             '( ( %s e. ( 0 ..^ %s ) /\\ %s ) -> %s )' % (R, DM, ALLI(R), CONCL))],
            'syl2anc', CONCL)
    exp1 = w.s([ex], 'ex', '( ( %s /\\ ( x e. ZZ /\\ y e. ZZ ) ) -> ( %s -> %s ) )'
               % (ANT0, EQ, CONCL))
    lim = w.s([exp1], 'rexlimdvva',
              '( %s -> ( E. x e. ZZ E. y e. ZZ %s -> %s ) )' % (ANT0, EQ, CONCL))
    s0 = mkst(w, ANT0)
    bz = s0([s0([], 'simp1', 'D e. NN')], 'nnzd', 'D e. ZZ')
    bm = s0([s0([], 'simp2', 'M e. NN')], 'nnzd', 'M e. ZZ')
    bez = s0([bz, bm, w.inst('bezout')], 'syl2anc', 'E. x e. ZZ E. y e. ZZ %s' % EQ)
    w.qed([lim, bez], 'mpd', '( %s -> %s )' % (ANT0, CONCL))
    return w


ANT = '( %s /\\ N e. NN0 )' % ANT0
CTD = CT('D')
CTXL = '{ x e. ( 1 ... N ) | ( ( x mod M ) = ( 1 mod M ) /\\ D || x ) }'
CTX = '{ x e. ( 1 ... N ) | ( x mod %s ) = o }' % DM
GOAL = '( abs ` ( ( # ` %s ) - ( N / %s ) ) ) <_ 1' % (CTD, DM)
LHSX = '( ( x mod M ) = ( 1 mod M ) /\\ D || x )'
RHSX = '( x mod %s ) = o' % DM


def crtcnt():
    w = W('crtcnt', 'The count of the integers up to N that are 1 mod M and divisible by '
                    'a D coprime to M is within 1 of N / ( D x. M ).')
    AO = '( %s /\\ ( o e. ( 0 ..^ %s ) /\\ %s ) )' % (ANT, DM, ALLI('o'))
    so = mkst(w, AO)
    ant = so([], 'simpl', ANT)
    ph0 = so([ant], 'simpld', ANT0)
    dnn = so([ph0], 'simp1d', 'D e. NN')
    mnn = so([ph0], 'simp2d', 'M e. NN')
    nn0 = so([ant], 'simprd', 'N e. NN0')
    dmn = so([dnn, mnn], 'nnmulcld', '%s e. NN' % DM)
    ofz = so([], 'simprl', 'o e. ( 0 ..^ %s )' % DM)
    alli = so([], 'simprr', ALLI('o'))
    cb1 = w.s([w.s([w.s([w.s([], 'oveq1', '( i = x -> ( i mod M ) = ( x mod M ) )')],
                        'eqeq1d', '( i = x -> ( ( i mod M ) = ( 1 mod M ) <-> ( x mod M ) = ( 1 mod M ) ) )'),
                    w.s([], 'breq2', '( i = x -> ( D || i <-> D || x ) )')], 'anbi12d',
                   '( i = x -> ( %s <-> %s ) )' % (LHS, LHSX))], 'cbvrabv',
              '%s = %s' % (CTD, CTXL))
    cb1d = so([cb1], 'a1i', '%s = %s' % (CTD, CTXL))
    # the pointwise equivalence at x
    AI = '( %s /\\ x e. ( 1 ... N ) )' % AO
    si = mkst(w, AI)
    ifz = si([], 'simpr', 'x e. ( 1 ... N )')
    iz = si([ifz, w.inst('elfzelz')], 'syl', 'x e. ZZ')
    sb = w.s([w.s([w.s([w.s([], 'oveq1', '( i = x -> ( i mod M ) = ( x mod M ) )')],
                       'eqeq1d', '( i = x -> ( ( i mod M ) = ( 1 mod M ) <-> ( x mod M ) = ( 1 mod M ) ) )'),
                   w.s([], 'breq2', '( i = x -> ( D || i <-> D || x ) )')], 'anbi12d',
                  '( i = x -> ( %s <-> %s ) )' % (LHS, LHSX)),
              w.s([w.s([], 'oveq1', '( i = x -> ( i mod %s ) = ( x mod %s ) )' % (DM, DM))],
                  'eqeq1d', '( i = x -> ( %s <-> %s ) )' % (RHS('o'), RHSX))], 'bibi12d',
             '( i = x -> ( ( %s <-> %s ) <-> ( %s <-> %s ) ) )' % (LHS, RHS('o'), LHSX, RHSX))
    rsp = w.s([sb], 'rspcv',
              '( x e. ZZ -> ( %s -> ( %s <-> %s ) ) )' % (ALLI('o'), LHSX, RHSX))
    rsp2 = si([iz, rsp], 'syl', '( %s -> ( %s <-> %s ) )' % (ALLI('o'), LHSX, RHSX))
    bic = si([lift(w, alli, AI), rsp2], 'mpd', '( %s <-> %s )' % (LHSX, RHSX))
    req = so([bic], 'rabbidva', '%s = %s' % (CTXL, CTX))
    seq = so([cb1d, req], 'eqtrd', '%s = %s' % (CTD, CTX))
    heq = so([seq], 'fveq2d', '( # ` %s ) = ( # ` %s )' % (CTD, CTX))
    cnt = so([nn0, dmn, ofz, w.inst('cntmod')], 'syl3anc',
             '( abs ` ( ( # ` %s ) - ( N / %s ) ) ) <_ 1' % (CTX, DM))
    e1 = so([heq], 'oveq1d',
            '( ( # ` %s ) - ( N / %s ) ) = ( ( # ` %s ) - ( N / %s ) )' % (CTD, DM, CTX, DM))
    e2 = so([e1], 'fveq2d',
            '( abs ` ( ( # ` %s ) - ( N / %s ) ) ) = ( abs ` ( ( # ` %s ) - ( N / %s ) ) )'
            % (CTD, DM, CTX, DM))
    main = so([e2, cnt], 'eqbrtrd', GOAL)
    lim = w.s([main], 'rexlimdvaa', '( %s -> ( %s -> %s ) )' % (ANT, CONCL, GOAL))
    sa = mkst(w, ANT)
    res = sa([sa([], 'simpl', ANT0), w.inst('crtres')], 'syl', CONCL)
    w.qed([lim, res], 'mpd', '( %s -> %s )' % (ANT, GOAL))
    return w


def main(names=None):
    fns = {'crtres': crtres, 'crtcnt': crtcnt}
    order = ['crtres', 'crtcnt']
    ok = True
    for nm in (names or order):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
