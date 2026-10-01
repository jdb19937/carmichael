"""Sortie v2b: the Selberg terms g( l ) and the bounding sum S.

vmulc     instantiation of the multiplicativity hypothesis at class arguments
vfprod    V of a product of distinct primes is the product of the values
vsqfprod  V ( D ) = prod over the prime divisors of D, for squarefree D
gtpos     0 < g( L ) for L || P
sspos     0 < S
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *


def PRD(X): return 'prod_ p e. %s p' % X
def VPRD(X): return 'prod_ p e. %s ( V ` p )' % X


def vmulc():
    w = W('vmulc', 'Instantiation of a multiplicativity hypothesis at two coprime arguments.')
    A = '( %s /\\ ( E e. NN /\\ F e. NN /\\ ( E gcd F ) = 1 ) )' % VMUL
    st = mkst(w, A)
    vm = st([], 'simpl', VMUL)
    en = st([], 'simpr1', 'E e. NN')
    fn = st([], 'simpr2', 'F e. NN')
    cop = st([], 'simpr3', '( E gcd F ) = 1')
    # substitution at a = E
    INN = 'A. b e. NN ( ( %s gcd b ) = 1 -> ( V ` ( %s x. b ) ) = ( ( V ` %s ) x. ( V ` b ) ) )'
    e1 = w.s([], 'oveq1', '( a = E -> ( a gcd b ) = ( E gcd b ) )')
    e2 = w.s([e1], 'eqeq1d', '( a = E -> ( ( a gcd b ) = 1 <-> ( E gcd b ) = 1 ) )')
    e3 = w.s([], 'oveq1', '( a = E -> ( a x. b ) = ( E x. b ) )')
    e4 = w.s([e3], 'fveq2d', '( a = E -> ( V ` ( a x. b ) ) = ( V ` ( E x. b ) ) )')
    e5 = w.s([], 'fveq2', '( a = E -> ( V ` a ) = ( V ` E ) )')
    e6 = w.s([e5], 'oveq1d',
             '( a = E -> ( ( V ` a ) x. ( V ` b ) ) = ( ( V ` E ) x. ( V ` b ) ) )')
    e7 = w.s([e4, e6], 'eqeq12d',
             '( a = E -> ( ( V ` ( a x. b ) ) = ( ( V ` a ) x. ( V ` b ) ) <-> '
             '( V ` ( E x. b ) ) = ( ( V ` E ) x. ( V ` b ) ) ) )')
    e8 = w.s([e2, e7], 'imbi12d',
             '( a = E -> ( ( ( a gcd b ) = 1 -> ( V ` ( a x. b ) ) = ( ( V ` a ) x. ( V ` b ) ) ) '
             '<-> ( ( E gcd b ) = 1 -> ( V ` ( E x. b ) ) = ( ( V ` E ) x. ( V ` b ) ) ) ) )')
    e9 = w.s([e8], 'ralbidv',
             '( a = E -> ( A. b e. NN ( ( a gcd b ) = 1 -> '
             '( V ` ( a x. b ) ) = ( ( V ` a ) x. ( V ` b ) ) ) <-> %s ) )'
             % (INN % ('E', 'E', 'E')))
    inner = st([e9, vm, en], 'rspcdva', INN % ('E', 'E', 'E'))
    # substitution at b = F
    f1 = w.s([], 'oveq2', '( b = F -> ( E gcd b ) = ( E gcd F ) )')
    f2 = w.s([f1], 'eqeq1d', '( b = F -> ( ( E gcd b ) = 1 <-> ( E gcd F ) = 1 ) )')
    f3 = w.s([], 'oveq2', '( b = F -> ( E x. b ) = ( E x. F ) )')
    f4 = w.s([f3], 'fveq2d', '( b = F -> ( V ` ( E x. b ) ) = ( V ` ( E x. F ) ) )')
    f5 = w.s([], 'fveq2', '( b = F -> ( V ` b ) = ( V ` F ) )')
    f6 = w.s([f5], 'oveq2d',
             '( b = F -> ( ( V ` E ) x. ( V ` b ) ) = ( ( V ` E ) x. ( V ` F ) ) )')
    f7 = w.s([f4, f6], 'eqeq12d',
             '( b = F -> ( ( V ` ( E x. b ) ) = ( ( V ` E ) x. ( V ` b ) ) <-> '
             '( V ` ( E x. F ) ) = ( ( V ` E ) x. ( V ` F ) ) ) )')
    f8 = w.s([f2, f7], 'imbi12d',
             '( b = F -> ( ( ( E gcd b ) = 1 -> ( V ` ( E x. b ) ) = ( ( V ` E ) x. ( V ` b ) ) ) '
             '<-> ( ( E gcd F ) = 1 -> ( V ` ( E x. F ) ) = ( ( V ` E ) x. ( V ` F ) ) ) ) )')
    imp = st([f8, inner, fn], 'rspcdva',
             '( ( E gcd F ) = 1 -> ( V ` ( E x. F ) ) = ( ( V ` E ) x. ( V ` F ) ) )')
    w.qed([imp, cop], 'mpd',
          '( %s -> ( V ` ( E x. F ) ) = ( ( V ` E ) x. ( V ` F ) ) )' % A)
    return w


PHIV = ('( ( %s /\\ {X} C_ Prime ) -> ( V ` ' + PRD('{X}') + ' ) = ' + VPRD('{X}') + ' )') % VH


def phiv(X):
    return ('( ( %s /\\ %s C_ Prime ) -> ( V ` %s ) = %s )' % (VH, X, PRD(X), VPRD(X)))


def vfprod():
    w = W('vfprod', 'The value of a multiplicative function at a product of distinct primes is '
                    'the product of its values at those primes.')
    YZ = '( y u. { z } )'

    def subst(X):
        e = 'x = %s' % X
        p1 = w.s([], 'prodeq1', '( %s -> %s = %s )' % (e, PRD('x'), PRD(X)))
        p2 = w.s([p1], 'fveq2d',
                 '( %s -> ( V ` %s ) = ( V ` %s ) )' % (e, PRD('x'), PRD(X)))
        p3 = w.s([], 'prodeq1', '( %s -> %s = %s )' % (e, VPRD('x'), VPRD(X)))
        p4 = w.s([p2, p3], 'eqeq12d',
                 '( %s -> ( ( V ` %s ) = %s <-> ( V ` %s ) = %s ) )'
                 % (e, PRD('x'), VPRD('x'), PRD(X), VPRD(X)))
        p5 = w.s([], 'sseq1', '( %s -> ( x C_ Prime <-> %s C_ Prime ) )' % (e, X))
        p6 = w.s([p5], 'anbi2d',
                 '( %s -> ( ( %s /\\ x C_ Prime ) <-> ( %s /\\ %s C_ Prime ) ) )'
                 % (e, VH, VH, X))
        return w.s([p6, p4], 'imbi12d', '( %s -> ( %s <-> %s ) )' % (e, phiv('x'), phiv(X)))

    h1 = subst('(/)')
    h2 = subst('y')
    h3 = subst(YZ)
    h4 = subst('T')
    # base case
    A0 = '( %s /\\ (/) C_ Prime )' % VH
    s0 = mkst(w, A0)
    v1 = s0([s0([], 'simpl', VH)], 'simp2d', '( V ` 1 ) = 1')
    pe = s0([w.s([], 'prod0', '%s = 1' % PRD('(/)'))], 'a1i', '%s = 1' % PRD('(/)'))
    pf = s0([pe], 'fveq2d', '( V ` %s ) = ( V ` 1 )' % PRD('(/)'))
    pv = s0([w.s([], 'prod0', '%s = 1' % VPRD('(/)'))], 'a1i', '%s = 1' % VPRD('(/)'))
    h5 = s0([s0([pf, v1], 'eqtrd', '( V ` %s ) = 1' % PRD('(/)')), pv], 'eqtr4d',
            '( V ` %s ) = %s' % (PRD('(/)'), VPRD('(/)')))
    # the induction step
    AST = '( y e. Fin /\\ -. z e. y )'
    VSS = '( %s /\\ %s C_ Prime )' % (VH, YZ)
    CS = '( %s /\\ %s )' % (AST, VSS)
    st = mkst(w, CS)
    yfin = w.s([], 'simpll', '( %s -> y e. Fin )' % CS)
    nz = w.s([], 'simplr', '( %s -> -. z e. y )' % CS)
    vh = w.s([], 'simprl', '( %s -> %s )' % (CS, VH))
    ssp = w.s([], 'simprr', '( %s -> %s C_ Prime )' % (CS, YZ))
    vf = st([vh], 'simp1d', 'V : NN --> RR')
    vmul = st([vh], 'simp3d', VMUL)
    ysyz = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    ysP = st([ysyz, ssp], 'sstrd', 'y C_ Prime')
    zyz = st([w.s([], 'ssun2', '{ z } C_ %s' % YZ),
              st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')], 'sselid',
             'z e. %s' % YZ)
    zP = st([ssp, zyz], 'sseldd', 'z e. Prime')
    zn = st([zP, w.inst('prmnn')], 'syl', 'z e. NN')
    zz = st([zn], 'nnzd', 'z e. ZZ')
    zc = st([zn], 'nncnd', 'z e. CC')
    vzr = st([vf, zn, w.inst('ffvelcdm')], 'syl2anc', '( V ` z ) e. RR')
    vzc = st([vzr], 'recnd', '( V ` z ) e. CC')
    # the product over y is a squarefree number with prime divisors exactly y
    sqp = st([yfin, ysP, w.inst('sqfprod')], 'syl2anc',
             '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = y )'
             % (PRD('y'), PRD('y'), PF(PRD('y'), 'q')))
    pnn = st([st([sqp], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PRD('y'), PRD('y')))],
             'simpld', '%s e. NN' % PRD('y'))
    ppf = st([sqp], 'simprd', '%s = y' % PF(PRD('y'), 'q'))
    pz = st([pnn], 'nnzd', '%s e. ZZ' % PRD('y'))
    # z does not divide the product over y
    elq = w.s([w.s([], 'breq1', '( q = z -> ( q || %s <-> z || %s ) )' % (PRD('y'), PRD('y')))],
              'elrab', '( z e. %s <-> ( z e. Prime /\\ z || %s ) )' % (PF(PRD('y'), 'q'), PRD('y')))
    mem = st([st([ppf], 'eleq2d', '( z e. %s <-> z e. y )' % PF(PRD('y'), 'q')),
              st([elq], 'a1i', '( z e. %s <-> ( z e. Prime /\\ z || %s ) )'
                 % (PF(PRD('y'), 'q'), PRD('y')))], 'bitr3d',
             '( ( z e. Prime /\\ z || %s ) <-> z e. y )' % PRD('y'))
    ndvd0 = st([nz, mem], 'mtbird', '-. ( z e. Prime /\\ z || %s )' % PRD('y'))
    CZ = '( %s /\\ z || %s )' % (CS, PRD('y'))
    sz = mkst(w, CZ)
    hz2 = sz([sz([zP], 'adantr', 'z e. Prime'), sz([], 'simpr', 'z || %s' % PRD('y'))], 'jca',
             '( z e. Prime /\\ z || %s )' % PRD('y'))
    nd = st([ndvd0, hz2], 'mtand', '-. z || %s' % PRD('y'))
    cop0 = st([zP, pz, w.inst('coprm')], 'syl2anc',
              '( -. z || %s <-> ( z gcd %s ) = 1 )' % (PRD('y'), PRD('y')))
    cop1 = st([cop0, nd], 'mpbid', '( z gcd %s ) = 1' % PRD('y'))
    cop = st([st([pz, zz, w.inst('gcdcom')], 'syl2anc',
                 '( %s gcd z ) = ( z gcd %s )' % (PRD('y'), PRD('y'))), cop1], 'eqtrd',
             '( %s gcd z ) = 1' % PRD('y'))
    vm = st([vmul, st([pnn, zn, cop], '3jca',
                      '( %s e. NN /\\ z e. NN /\\ ( %s gcd z ) = 1 )' % (PRD('y'), PRD('y'))),
             w.inst('vmulc')], 'syl2anc',
            '( V ` ( %s x. z ) ) = ( ( V ` %s ) x. ( V ` z ) )' % (PRD('y'), PRD('y')))
    # the two products split off z
    nfp = w.s([], 'nfv', 'F/ p %s' % CS)
    nfz = w.s([], 'nfcv', 'F/_ p z')
    nfvz = w.s([], 'nfcv', 'F/_ p ( V ` z )')
    zex = st([w.s([], 'vex', 'z e. _V')], 'a1i', 'z e. _V')
    BY = '( %s /\\ p e. y )' % CS
    fy = mkst(w, BY)
    pP = fy([fy([ysP], 'adantr', 'y C_ Prime'), fy([], 'simpr', 'p e. y')], 'sseldd', 'p e. Prime')
    pn = fy([pP, w.inst('prmnn')], 'syl', 'p e. NN')
    pc = fy([pn], 'nncnd', 'p e. CC')
    vpr = fy([fy([vf], 'adantr', 'V : NN --> RR'), pn, w.inst('ffvelcdm')], 'syl2anc',
             '( V ` p ) e. RR')
    vpc = fy([vpr], 'recnd', '( V ` p ) e. CC')
    idp = w.s([], 'id', '( p = z -> p = z )')
    fvp = w.s([], 'fveq2', '( p = z -> ( V ` p ) = ( V ` z ) )')
    spl1 = st([nfp, nfz, yfin, zex, nz, pc, idp, zc], 'fprodsplitsn',
              '%s = ( %s x. z )' % (PRD(YZ), PRD('y')))
    spl2 = st([nfp, nfvz, yfin, zex, nz, vpc, fvp, vzc], 'fprodsplitsn',
              '%s = ( %s x. ( V ` z ) )' % (VPRD(YZ), VPRD('y')))
    # put the induction hypothesis in
    CI = '( %s /\\ %s )' % (CS, phiv('y'))
    si = mkst(w, CI)
    ih = si([si([], 'simpr', phiv('y')),
             si([si([vh], 'adantr', VH), si([ysP], 'adantr', 'y C_ Prime')], 'jca',
                '( %s /\\ y C_ Prime )' % VH)], 'mpd',
            '( V ` %s ) = %s' % (PRD('y'), VPRD('y')))
    e1 = si([si([spl1], 'adantr', '%s = ( %s x. z )' % (PRD(YZ), PRD('y')))], 'fveq2d',
            '( V ` %s ) = ( V ` ( %s x. z ) )' % (PRD(YZ), PRD('y')))
    e2 = si([vm], 'adantr', '( V ` ( %s x. z ) ) = ( ( V ` %s ) x. ( V ` z ) )'
            % (PRD('y'), PRD('y')))
    e3 = si([ih], 'oveq1d',
            '( ( V ` %s ) x. ( V ` z ) ) = ( %s x. ( V ` z ) )' % (PRD('y'), VPRD('y')))
    e4 = si([spl2], 'adantr', '%s = ( %s x. ( V ` z ) )' % (VPRD(YZ), VPRD('y')))
    concl = si([si([si([e1, e2], 'eqtrd',
                       '( V ` %s ) = ( ( V ` %s ) x. ( V ` z ) )' % (PRD(YZ), PRD('y'))), e3],
                   'eqtrd', '( V ` %s ) = ( %s x. ( V ` z ) )' % (PRD(YZ), VPRD('y'))), e4],
               'eqtr4d', '( V ` %s ) = %s' % (PRD(YZ), VPRD(YZ)))
    x1 = w.s([concl], 'ex', '( %s -> ( %s -> ( V ` %s ) = %s ) )'
             % (CS, phiv('y'), PRD(YZ), VPRD(YZ)))
    x2 = w.s([x1], 'ex', '( %s -> ( %s -> ( %s -> ( V ` %s ) = %s ) ) )'
             % (AST, VSS, phiv('y'), PRD(YZ), VPRD(YZ)))
    h6 = w.s([x2], 'com23', '( %s -> ( %s -> %s ) )' % (AST, phiv('y'), phiv(YZ)))
    res = w.s([h1, h2, h3, h4, h5, h6], 'findcard2s', '( T e. Fin -> %s )' % phiv('T'))
    # assemble
    AF = '( %s /\\ ( T e. Fin /\\ T C_ Prime ) )' % VH
    sf = mkst(w, AF)
    tfin = sf([], 'simprl', 'T e. Fin')
    vhf = sf([], 'simpl', VH)
    sspf = sf([], 'simprr', 'T C_ Prime')
    fin = sf([sf([res], 'a1i', '( T e. Fin -> %s )' % phiv('T')), tfin], 'mpd', phiv('T'))
    w.qed([fin, sf([vhf, sspf], 'jca', '( %s /\\ T C_ Prime )' % VH)], 'mpd',
          '( %s -> ( V ` %s ) = %s )' % (AF, PRD('T'), VPRD('T')))
    return w


def vprmc():
    w = W('vprmc', 'Instantiation of the density condition at a prime divisor of the sifting '
                   'product.')
    A = '( %s /\ ( Q e. Prime /\ Q || P ) )' % VPRM
    st = mkst(w, A)
    vp = st([], 'simpl', VPRM)
    qp = st([], 'simprl', 'Q e. Prime')
    qd = st([], 'simprr', 'Q || P')
    e1 = w.s([], 'breq1', '( s = Q -> ( s || P <-> Q || P ) )')
    e2 = w.s([], 'fveq2', '( s = Q -> ( V ` s ) = ( V ` Q ) )')
    e3 = w.s([e2], 'breq2d', '( s = Q -> ( 0 < ( V ` s ) <-> 0 < ( V ` Q ) ) )')
    e4 = w.s([e2], 'breq1d', '( s = Q -> ( ( V ` s ) < 1 <-> ( V ` Q ) < 1 ) )')
    e5 = w.s([e3, e4], 'anbi12d',
             '( s = Q -> ( ( 0 < ( V ` s ) /\ ( V ` s ) < 1 ) <-> '
             '( 0 < ( V ` Q ) /\ ( V ` Q ) < 1 ) ) )')
    e6 = w.s([e1, e5], 'imbi12d',
             '( s = Q -> ( ( s || P -> ( 0 < ( V ` s ) /\ ( V ` s ) < 1 ) ) <-> '
             '( Q || P -> ( 0 < ( V ` Q ) /\ ( V ` Q ) < 1 ) ) ) )')
    imp = st([e6, vp, qp], 'rspcdva',
             '( Q || P -> ( 0 < ( V ` Q ) /\ ( V ` Q ) < 1 ) )')
    w.qed([imp, qd], 'mpd',
          '( %s -> ( 0 < ( V ` Q ) /\ ( V ` Q ) < 1 ) )' % A)
    return w


def vsqfprod():
    w = W('vsqfprod', 'The value of a multiplicative function at a squarefree number is the '
                      'product of its values at the prime divisors.')
    A = '( %s /\ ( D e. NN /\ ( mmu ` D ) =/= 0 ) )' % VH
    TR = PF('D', 'r')
    TQ = PF('D', 'q')
    st = mkst(w, A)
    vh = st([], 'simpl', VH)
    dnn = st([], 'simprl', 'D e. NN')
    dsq = st([], 'simprr', '( mmu ` D ) =/= 0')
    cbvq = st([w.s([], 'cbvrabv', '%s = %s' % (TQ, TR))], 'a1i', '%s = %s' % (TQ, TR))
    cbvp = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), TR))], 'a1i',
              '%s = %s' % (PF('D', 'p'), TR))
    finp = st([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    fin = st([cbvp, finp], 'eqeltrrd', '%s e. Fin' % TR)
    ssp = st([w.s([], 'ssrab2', '%s C_ Prime' % TR)], 'a1i', '%s C_ Prime' % TR)
    vfp = st([vh, st([fin, ssp], 'jca', '( %s e. Fin /\ %s C_ Prime )' % (TR, TR)),
              w.inst('vfprod')], 'syl2anc',
             '( V ` %s ) = %s' % (PRD(TR), VPRD(TR)))
    pid = st([st([dnn, dsq], 'jca', '( D e. NN /\ ( mmu ` D ) =/= 0 )'),
              w.inst('sqfprodid')], 'syl', '%s = D' % PRD(TQ))
    pcv = st([cbvq], 'prodeq1d', '%s = %s' % (PRD(TQ), PRD(TR)))
    pidr = st([pcv, pid], 'eqtr3d', '%s = D' % PRD(TR))
    fv = st([pidr], 'fveq2d', '( V ` %s ) = ( V ` D )' % PRD(TR))
    w.qed([fv, vfp], 'eqtr3d', '( %s -> ( V ` D ) = %s )' % (A, VPRD(TR)))
    return w


def gtpos():
    w = W('gtpos', 'The Selberg term of a divisor of the sifting product is positive.')
    A = '( %s /\ ( L e. NN /\ L || P ) )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    TR = PF('L', 'r')
    lnn = st([], 'simprl', 'L e. NN')
    ldp = st([], 'simprr', 'L || P')
    lsq = st([st([d['pnn'], lnn, ldp], '3jca', '( P e. NN /\ L e. NN /\ L || P )'),
              w.inst('dvdssqf')], 'syl',
             '( ( mmu ` P ) =/= 0 -> ( mmu ` L ) =/= 0 )')
    lsqf = st([lsq, d['psqf']], 'mpd', '( mmu ` L ) =/= 0')
    # ( V ` L ) = prod_ p e. PF( L ) ( V ` p ), and each factor is positive
    vp = st([d['vh'], st([lnn, lsqf], 'jca', '( L e. NN /\ ( mmu ` L ) =/= 0 )'),
             w.inst('vsqfprod')], 'syl2anc', '( V ` L ) = %s' % VPRD(TR))
    # facts about a prime divisor q of L, under the antecedent extended by q e. PF( L )
    for var, ante_var in (('p', 'p'), ('q', 'q')):
        pass
    def primefacts(v):
        B = '( %s /\ %s e. %s )' % (A, v, TR)
        sb = mkst(w, B)
        elr = w.s([w.s([], 'breq1', '( r = %s -> ( r || L <-> %s || L ) )' % (v, v))], 'elrab',
                  '( %s e. %s <-> ( %s e. Prime /\ %s || L ) )' % (v, TR, v, v))
        mem = sb([], 'simpr', '%s e. %s' % (v, TR))
        conj = sb([sb([elr], 'a1i', '( %s e. %s <-> ( %s e. Prime /\ %s || L ) )' % (v, TR, v, v)),
                   mem], 'mpbid', '( %s e. Prime /\ %s || L )' % (v, v))
        qprm = sb([conj], 'simpld', '%s e. Prime' % v)
        qdl = sb([conj], 'simprd', '%s || L' % v)
        qz = sb([qprm, w.inst('prmz')], 'syl', '%s e. ZZ' % v)
        lz = sb([sb([lnn], 'adantr', 'L e. NN')], 'nnzd', 'L e. ZZ')
        pz = sb([sb([d['pnn']], 'adantr', 'P e. NN')], 'nnzd', 'P e. ZZ')
        qdp = sb([sb([qz, lz, pz, w.inst('dvdstr')], 'syl3anc',
                     '( ( %s || L /\ L || P ) -> %s || P )' % (v, v)),
                  sb([qdl, sb([ldp], 'adantr', 'L || P')], 'jca',
                     '( %s || L /\ L || P )' % v)], 'mpd', '%s || P' % v)
        both = sb([sb([d['vprm']], 'adantr', VPRM),
                   sb([qprm, qdp], 'jca', '( %s e. Prime /\ %s || P )' % (v, v)),
                   w.inst('vprmc')], 'syl2anc',
                  '( 0 < ( V ` %s ) /\ ( V ` %s ) < 1 )' % (v, v))
        pos = sb([both], 'simpld', '0 < ( V ` %s )' % v)
        lt1 = sb([both], 'simprd', '( V ` %s ) < 1' % v)
        vre = sb([sb([sb([d['vf']], 'adantr', 'V : NN --> RR'),
                      sb([qprm, w.inst('prmnn')], 'syl', '%s e. NN' % v)], 'jca',
                     '( V : NN --> RR /\ %s e. NN )' % v), w.inst('ffvelcdm')], 'syl',
                 '( V ` %s ) e. RR' % v)
        return sb, pos, lt1, vre
    sbp, posp, _, vrep = primefacts('p')
    vrp = sbp([vrep, posp], 'elrpd', '( V ` p ) e. RR+')
    fin = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('L', 'p'), TR))], 'a1i',
                 '%s = %s' % (PF('L', 'p'), TR)),
              st([lnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('L', 'p'))],
             'eqeltrrd', '%s e. Fin' % TR)
    prp = st([fin, vrp], 'fprodrpcl', '%s e. RR+' % VPRD(TR))
    vlrp = st([vp, prp], 'eqeltrd', '( V ` L ) e. RR+')
    # the second factor
    if not need_prod:
        return vlrp, None
    sbq, _, lt1q, vreq = primefacts('q')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % ('( %s /\ q e. %s )' % (A, TR)))
    sub = sbq([sbq([vreq, one], 'posdifd',
                   '( ( V ` q ) < 1 <-> 0 < ( 1 - ( V ` q ) ) )'), lt1q], 'mpbid',
              '0 < ( 1 - ( V ` q ) )')
    subr = sbq([one, vreq], 'resubcld', '( 1 - ( V ` q ) ) e. RR')
    subrp = sbq([subr, sub], 'elrpd', '( 1 - ( V ` q ) ) e. RR+')
    recrp = sbq([subrp], 'rpreccld', '( 1 / ( 1 - ( V ` q ) ) ) e. RR+')
    prq = st([fin, recrp], 'fprodrpcl',
             'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) e. RR+' % TR)
    tot = st([vlrp, prq], 'rpmulcld', '%s e. RR+' % GT('L'))
    w.qed([tot], 'rpgt0d', '( %s -> 0 < %s )' % (A, GT('L')))
    return w


def _gtrpbody(w, A, d, st, need_prod=True):
    """( A -> GT( L ) e. RR+ ), for A implying SH and ( L e. NN /\ L || P )"""
    TR = PF('L', 'r')
    lnn = st([], 'simprl', 'L e. NN')
    ldp = st([], 'simprr', 'L || P')
    lsqf = st([st([st([d['pnn'], lnn, ldp], '3jca', '( P e. NN /\ L e. NN /\ L || P )'),
                   w.inst('dvdssqf')], 'syl',
                  '( ( mmu ` P ) =/= 0 -> ( mmu ` L ) =/= 0 )'), d['psqf']], 'mpd',
              '( mmu ` L ) =/= 0')
    vp = st([d['vh'], st([lnn, lsqf], 'jca', '( L e. NN /\ ( mmu ` L ) =/= 0 )'),
             w.inst('vsqfprod')], 'syl2anc', '( V ` L ) = %s' % VPRD(TR))

    def primefacts(v):
        B = '( %s /\ %s e. %s )' % (A, v, TR)
        sb = mkst(w, B)
        elr = w.s([w.s([], 'breq1', '( r = %s -> ( r || L <-> %s || L ) )' % (v, v))], 'elrab',
                  '( %s e. %s <-> ( %s e. Prime /\ %s || L ) )' % (v, TR, v, v))
        conj = sb([sb([elr], 'a1i', '( %s e. %s <-> ( %s e. Prime /\ %s || L ) )' % (v, TR, v, v)),
                   sb([], 'simpr', '%s e. %s' % (v, TR))], 'mpbid',
                  '( %s e. Prime /\ %s || L )' % (v, v))
        qprm = sb([conj], 'simpld', '%s e. Prime' % v)
        qdl = sb([conj], 'simprd', '%s || L' % v)
        qz = sb([qprm, w.inst('prmz')], 'syl', '%s e. ZZ' % v)
        lz = sb([sb([lnn], 'adantr', 'L e. NN')], 'nnzd', 'L e. ZZ')
        pz = sb([sb([d['pnn']], 'adantr', 'P e. NN')], 'nnzd', 'P e. ZZ')
        qdp = sb([sb([qz, lz, pz, w.inst('dvdstr')], 'syl3anc',
                     '( ( %s || L /\ L || P ) -> %s || P )' % (v, v)),
                  sb([qdl, sb([ldp], 'adantr', 'L || P')], 'jca',
                     '( %s || L /\ L || P )' % v)], 'mpd', '%s || P' % v)
        both = sb([sb([d['vprm']], 'adantr', VPRM),
                   sb([qprm, qdp], 'jca', '( %s e. Prime /\ %s || P )' % (v, v)),
                   w.inst('vprmc')], 'syl2anc',
                  '( 0 < ( V ` %s ) /\ ( V ` %s ) < 1 )' % (v, v))
        pos = sb([both], 'simpld', '0 < ( V ` %s )' % v)
        lt1 = sb([both], 'simprd', '( V ` %s ) < 1' % v)
        vre = sb([sb([sb([d['vf']], 'adantr', 'V : NN --> RR'),
                      sb([qprm, w.inst('prmnn')], 'syl', '%s e. NN' % v)], 'jca',
                     '( V : NN --> RR /\ %s e. NN )' % v), w.inst('ffvelcdm')], 'syl',
                 '( V ` %s ) e. RR' % v)
        return sb, pos, lt1, vre

    sbp, posp, _, vrep = primefacts('p')
    vrp = sbp([vrep, posp], 'elrpd', '( V ` p ) e. RR+')
    fin = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('L', 'p'), TR))], 'a1i',
                 '%s = %s' % (PF('L', 'p'), TR)),
              st([lnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('L', 'p'))],
             'eqeltrrd', '%s e. Fin' % TR)
    prp = st([fin, vrp], 'fprodrpcl', '%s e. RR+' % VPRD(TR))
    vlrp = st([vp, prp], 'eqeltrd', '( V ` L ) e. RR+')
    if not need_prod:
        return vlrp, None
    sbq, _, lt1q, vreq = primefacts('q')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % ('( %s /\ q e. %s )' % (A, TR)))
    sub = sbq([sbq([vreq, one], 'posdifd',
                   '( ( V ` q ) < 1 <-> 0 < ( 1 - ( V ` q ) ) )'), lt1q], 'mpbid',
              '0 < ( 1 - ( V ` q ) )')
    subr = sbq([one, vreq], 'resubcld', '( 1 - ( V ` q ) ) e. RR')
    subrp = sbq([subr, sub], 'elrpd', '( 1 - ( V ` q ) ) e. RR+')
    recrp = sbq([subrp], 'rpreccld', '( 1 / ( 1 - ( V ` q ) ) ) e. RR+')
    prq = st([fin, recrp], 'fprodrpcl',
             'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) e. RR+' % TR)
    return vlrp, prq


def gtrp():
    w = W('gtrp', 'The Selberg term of a divisor of the sifting product is a positive real.')
    A = '( %s /\ ( L e. NN /\ L || P ) )' % SH
    d = shsteps(w, A, (SH,))
    vlrp, prq = _gtrpbody(w, A, d, d['st'])
    w.qed([vlrp, prq], 'rpmulcld', '( %s -> %s e. RR+ )' % (A, GT('L')))
    return w


def vdrp():
    w = W('vdrp', 'The density at a divisor of the sifting product is a positive real.')
    A = '( %s /\ ( L e. NN /\ L || P ) )' % SH
    d = shsteps(w, A, (SH,))
    vlrp, _ = _gtrpbody(w, A, d, d['st'], need_prod=False)
    w.qed([d['st']([], 'eqidd', '( V ` L ) = ( V ` L )'), vlrp], 'eqeltrd',
          '( %s -> ( V ` L ) e. RR+ )' % A)
    return w


def ssrp():
    w = W('ssrp', 'The Selberg bounding sum is a positive real.')
    A = SH
    d = shsteps(w, A, ())
    st = d['st']
    DP = DV('P')
    TERM = SSTERM('l')
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DP)
    B = '( %s /\ l e. %s )' % (A, DP)
    sb = mkst(w, B)
    elr = w.s([w.s([], 'breq1', '( x = l -> ( x || P <-> l || P ) )')], 'elrab',
              '( l e. %s <-> ( l e. NN /\ l || P ) )' % DP)
    conj = sb([sb([elr], 'a1i', '( l e. %s <-> ( l e. NN /\ l || P ) )' % DP),
               sb([], 'simpr', 'l e. %s' % DP)], 'mpbid', '( l e. NN /\ l || P )')
    both = sb([sb([d['sh']], 'adantr', SH), conj, w.inst('ssterm')], 'syl2anc',
              '( %s e. RR /\ 0 <_ %s )' % (TERM, TERM))
    tre = sb([both], 'simpld', '%s e. RR' % TERM)
    ssre = st([finP, tre], 'fsumrecl', '%s e. RR' % SS())
    pos = st([d['sh'], w.inst('sspos')], 'syl', '0 < %s' % SS())
    w.qed([ssre, pos], 'elrpd', '( %s -> %s e. RR+ )' % (A, SS()))
    return w


def ssterm():
    w = W('ssterm', 'The summand of the Selberg bounding sum is a nonnegative real.')
    A = '( %s /\ ( L e. NN /\ L || P ) )' % SH
    T = SSTERM('L')
    d = shsteps(w, A, (SH,))
    st = d['st']
    rp = st([d['sh'], st([], 'simpr', '( L e. NN /\ L || P )'), w.inst('gtrp')], 'syl2anc',
            '%s e. RR+' % GT('L'))
    gre = st([rp], 'rpred', '%s e. RR' % GT('L'))
    gge = st([rp], 'rpge0d', '0 <_ %s' % GT('L'))
    BT = '( %s /\ ( L ^ 2 ) <_ Y )' % A
    bt = mkst(w, BT)
    t1 = bt([], 'iftrued', '%s = %s' % (T, GT('L')))
    r1 = bt([t1, bt([gre], 'adantr', '%s e. RR' % GT('L'))], 'eqeltrd', '%s e. RR' % T)
    n1 = bt([bt([gge], 'adantr', '0 <_ %s' % GT('L')), t1], 'breqtrrd', '0 <_ %s' % T)
    BF = '( %s /\ -. ( L ^ 2 ) <_ Y )' % A
    bf = mkst(w, BF)
    t2 = bf([], 'iffalsed', '%s = 0' % T)
    r2 = bf([t2, bf([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR')], 'eqeltrd', '%s e. RR' % T)
    n2 = bf([bf([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0'), t2], 'breqtrrd', '0 <_ %s' % T)
    re = st([r1, r2], 'pm2.61dan', '%s e. RR' % T)
    ge = st([n1, n2], 'pm2.61dan', '0 <_ %s' % T)
    w.qed([re, ge], 'jca', '( %s -> ( %s e. RR /\ 0 <_ %s ) )' % (A, T, T))
    return w


def sspos():
    w = W('sspos', 'The Selberg bounding sum is positive.')
    A = SH
    d = shsteps(w, A, ())
    st = d['st']
    DP = DV('P')
    TERM = SSTERM('l')
    ONE = SSTERM('1')
    REST = '( %s \ { 1 } )' % DP
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DP)

    def termfacts(ante, memstep, shstep):
        """( ante -> TERM e. RR ) and ( ante -> 0 <_ TERM ) from ( ante -> l e. DV( P ) )"""
        sb = mkst(w, ante)
        elr = w.s([w.s([], 'breq1', '( x = l -> ( x || P <-> l || P ) )')], 'elrab',
                  '( l e. %s <-> ( l e. NN /\ l || P ) )' % DP)
        conj = sb([sb([elr], 'a1i', '( l e. %s <-> ( l e. NN /\ l || P ) )' % DP), memstep],
                  'mpbid', '( l e. NN /\ l || P )')
        both = sb([shstep, conj, w.inst('ssterm')], 'syl2anc',
                  '( %s e. RR /\ 0 <_ %s )' % (TERM, TERM))
        return sb([both], 'simpld', '%s e. RR' % TERM), sb([both], 'simprd', '0 <_ %s' % TERM)

    B = '( %s /\ l e. %s )' % (A, DP)
    tre, tge = termfacts(B, w.s([], 'simpr', '( %s -> l e. %s )' % (B, DP)),
                         w.s([], 'simpl', '( %s -> %s )' % (B, SH)))
    tcn = w.s([tre], 'recnd', '( %s -> %s e. CC )' % (B, TERM))
    # split off l = 1
    onenn = st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    onedp = st([w.s([w.s([], 'breq1', '( x = 1 -> ( x || P <-> 1 || P ) )')], 'elrab',
                    '( 1 e. %s <-> ( 1 e. NN /\ 1 || P ) )' % DP),
                st([onenn, st([st([d['pnn']], 'nnzd', 'P e. ZZ'), w.inst('1dvds')], 'syl',
                              '1 || P')], 'jca', '( 1 e. NN /\ 1 || P )')], 'sylibr',
               '1 e. %s' % DP)
    sn = st([onedp], 'snssd', '{ 1 } C_ %s' % DP)
    un = st([st([w.s([], 'undif', '( { 1 } C_ %s <-> ( { 1 } u. %s ) = %s )' % (DP, REST, DP))],
                'a1i', '( { 1 } C_ %s <-> ( { 1 } u. %s ) = %s )' % (DP, REST, DP)), sn],
            'mpbid', '( { 1 } u. %s ) = %s' % (REST, DP))
    unr = st([un], 'eqcomd', '%s = ( { 1 } u. %s )' % (DP, REST))
    dsj = st([w.s([], 'disjdif', '( { 1 } i^i %s ) = (/)' % REST)], 'a1i',
             '( { 1 } i^i %s ) = (/)' % REST)
    spl = st([dsj, unr, finP, tcn], 'fsumsplit',
             '%s = ( sum_ l e. { 1 } %s + sum_ l e. %s %s )' % (SS(), TERM, REST, TERM))
    # the singleton term is 1
    rgen = w.s([w.s([], 'nprmdvds1', '( r e. Prime -> -. r || 1 )')], 'rgen',
               'A. r e. Prime -. r || 1')
    pf1 = w.s([w.s([], 'rabeq0', '( %s = (/) <-> A. r e. Prime -. r || 1 )' % PF('1', 'r')),
               rgen], 'mpbir', '%s = (/)' % PF('1', 'r'))
    pr0 = w.s([w.s([pf1], 'prodeq1i',
                   'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) = '
                   'prod_ q e. (/) ( 1 / ( 1 - ( V ` q ) ) )' % PF('1', 'r')),
               w.s([], 'prod0', 'prod_ q e. (/) ( 1 / ( 1 - ( V ` q ) ) ) = 1')], 'eqtri',
              'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) = 1' % PF('1', 'r'))
    gt1 = st([st([d['v1'], st([pr0], 'a1i',
                              'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) = 1' % PF('1', 'r'))],
                 'oveq12d', '%s = ( 1 x. 1 )' % GT('1')),
              st([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')], 'eqtrd',
             '%s = 1' % GT('1'))
    sqone = st([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')
    cond = st([sqone, d['y1']], 'eqbrtrd', '( 1 ^ 2 ) <_ Y')
    onee = st([st([cond], 'iftrued', '%s = %s' % (ONE, GT('1'))), gt1], 'eqtrd', '%s = 1' % ONE)
    TRL = PF('l', 'r')
    subst = w.s([w.s([], 'oveq1', '( l = 1 -> ( l ^ 2 ) = ( 1 ^ 2 ) )')], 'breq1d',
                '( l = 1 -> ( ( l ^ 2 ) <_ Y <-> ( 1 ^ 2 ) <_ Y ) )')
    sub2 = w.s([w.s([], 'fveq2', '( l = 1 -> ( V ` l ) = ( V ` 1 ) )'),
                w.s([w.s([w.s([], 'breq2', '( l = 1 -> ( r || l <-> r || 1 ) )')], 'rabbidv',
                         '( l = 1 -> %s = %s )' % (TRL, PF('1', 'r')))], 'prodeq1d',
                    '( l = 1 -> prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) = '
                    'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) )' % (TRL, PF('1', 'r')))],
               'oveq12d', '( l = 1 -> %s = %s )' % (GT('l'), GT('1')))
    sub3 = w.s([subst, sub2], 'ifbieq1d', '( l = 1 -> %s = %s )' % (TERM, ONE))
    onecc = st([onee, st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'eqeltrd',
               '%s e. CC' % ONE)
    inst = w.s([sub3], 'sumsn',
               '( ( 1 e. _V /\ %s e. CC ) -> sum_ l e. { 1 } %s = %s )' % (ONE, TERM, ONE))
    snsum = st([st([w.s([], '1ex', '1 e. _V')], 'a1i', '1 e. _V'), onecc, inst], 'syl2anc',
               'sum_ l e. { 1 } %s = %s' % (TERM, ONE))
    snval = st([snsum, onee], 'eqtrd', 'sum_ l e. { 1 } %s = 1' % TERM)
    # the rest is nonnegative
    CR = '( %s /\ l e. %s )' % (A, REST)
    cr = mkst(w, CR)
    inDP = cr([cr([w.s([], 'difss', '%s C_ %s' % (REST, DP))], 'a1i', '%s C_ %s' % (REST, DP)),
               cr([], 'simpr', 'l e. %s' % REST)], 'sseldd', 'l e. %s' % DP)
    tre2, tge2 = termfacts(CR, inDP, w.s([], 'simpl', '( %s -> %s )' % (CR, SH)))
    restfin = st([finP, w.inst('diffi')], 'syl', '%s e. Fin' % REST)
    rest0 = st([restfin, tre2, tge2], 'fsumge0', '0 <_ sum_ l e. %s %s' % (REST, TERM))
    restre = st([restfin, tre2], 'fsumrecl', 'sum_ l e. %s %s e. RR' % (REST, TERM))
    onere = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    lt01 = st([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1')
    pos = st([onere, restre, lt01, rest0], 'addgtge0d',
             '0 < ( 1 + sum_ l e. %s %s )' % (REST, TERM))
    eq = st([snval], 'oveq1d',
            '( sum_ l e. { 1 } %s + sum_ l e. %s %s ) = ( 1 + sum_ l e. %s %s )'
            % (TERM, REST, TERM, REST, TERM))
    w.qed([pos, st([spl, eq], 'eqtrd',
                   '%s = ( 1 + sum_ l e. %s %s )' % (SS(), REST, TERM))], 'breqtrrd',
          '( %s -> 0 < %s )' % (A, SS()))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['vmulc']:
        globals()[f]().run()
