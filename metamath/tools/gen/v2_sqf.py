"""Sortie v2: products of distinct primes (sqfmul, sqfprod, sqfprodid)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

def PF(X, v='q'): return '{ %s e. Prime | %s || %s }' % (v, v, X)
def OM(X): return '( # ` %s )' % PF(X)
AM = ('( ( E e. NN /\\ ( mmu ` E ) =/= 0 /\\ %s = S ) /\\ ( Z e. Prime /\\ -. Z e. S ) )'
      % PF('E'))
EZ = '( E x. Z )'


def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))


def sqfmul():
    w = W('sqfmul',
          'Multiplying a squarefree number by a prime that does not divide it keeps it squarefree '
          'and adjoins the prime to its set of prime divisors.')
    A = AM
    st = mkst(w, A)
    e = st([], 'simpl1', 'E e. NN')
    sq = st([], 'simpl2', '( mmu ` E ) =/= 0')
    pfe = st([], 'simpl3', '%s = S' % PF('E'))
    z = st([], 'simprl', 'Z e. Prime')
    nzs = st([], 'simprr', '-. Z e. S')
    zn = st([z, w.inst('prmnn')], 'syl', 'Z e. NN')
    zz = st([z, w.inst('prmz')], 'syl', 'Z e. ZZ')
    ez = st([e], 'nnzd', 'E e. ZZ')
    ezn = st([e, zn], 'nnmulcld', '%s e. NN' % EZ)
    eznz = st([ezn], 'nnzd', '%s e. ZZ' % EZ)
    sqz = st([z, w.inst('sqfprm')], 'syl', '( mmu ` Z ) =/= 0')
    # Z does not divide E
    pfeq = st([pfe], 'eleq2d', '( Z e. %s <-> Z e. S )' % PF('E'))
    nzpf = st([pfeq, nzs], 'mtbird', '-. Z e. %s' % PF('E'))
    eli = w.s([], 'breq1', '( q = Z -> ( q || E <-> Z || E ) )')
    elr = w.s([eli], 'elrab', '( Z e. %s <-> ( Z e. Prime /\\ Z || E ) )' % PF('E'))
    conj = st([st([elr], 'a1i', '( Z e. %s <-> ( Z e. Prime /\\ Z || E ) )' % PF('E')), nzpf],
              'mtbid', '-. ( Z e. Prime /\\ Z || E )')
    CD = '( %s /\\ Z || E )' % A
    jc = w.s([w.s([z], 'adantr', '( %s -> Z e. Prime )' % CD),
              w.s([], 'simpr', '( %s -> Z || E )' % CD)], 'jca',
             '( %s -> ( Z e. Prime /\\ Z || E ) )' % CD)
    ndv = st([conj, jc], 'mtand', '-. Z || E')
    # coprimality and squarefreeness of the product
    cop = st([st([z, ez, w.inst('coprm')], 'syl2anc',
                 '( -. Z || E <-> ( Z gcd E ) = 1 )'), ndv], 'mpbid', '( Z gcd E ) = 1')
    cop2 = st([st([zz, ez, w.inst('gcdcom')], 'syl2anc', '( Z gcd E ) = ( E gcd Z )'), cop],
              'eqtr3d', '( E gcd Z ) = 1')
    sqez = st([st([e, zn, cop2], '3jca', '( E e. NN /\\ Z e. NN /\\ ( E gcd Z ) = 1 )'),
               st([sq, sqz], 'jca', '( ( mmu ` E ) =/= 0 /\\ ( mmu ` Z ) =/= 0 )'),
               w.inst('mumullem2')], 'syl2anc', '( mmu ` %s ) =/= 0' % EZ)
    # the set of prime divisors
    elrz = w.s([w.s([], 'breq1', '( q = r -> ( q || %s <-> r || %s ) )' % (EZ, EZ))], 'elrab',
               '( r e. %s <-> ( r e. Prime /\\ r || %s ) )' % (PF(EZ), EZ))
    elre = w.s([w.s([], 'breq1', '( q = r -> ( q || E <-> r || E ) )')], 'elrab',
               '( r e. %s <-> ( r e. Prime /\\ r || E ) )' % PF('E'))
    # forward
    CF = '( %s /\\ r e. %s )' % (A, PF(EZ))
    sf = mkst(w, CF)
    rin = sf([], 'simpr', 'r e. %s' % PF(EZ))
    rp = sf([sf([elrz], 'a1i', '( r e. %s <-> ( r e. Prime /\\ r || %s ) )' % (PF(EZ), EZ)), rin],
            'mpbid', '( r e. Prime /\\ r || %s )' % EZ)
    rpr = sf([rp], 'simpld', 'r e. Prime')
    rdv = sf([rp], 'simprd', 'r || %s' % EZ)
    euc = sf([rpr, sf([ez], 'adantr', 'E e. ZZ'), sf([zz], 'adantr', 'Z e. ZZ'),
              w.inst('euclemma')], 'syl3anc',
             '( r || %s <-> ( r || E \\/ r || Z ) )' % EZ)
    dis = sf([euc, rdv], 'mpbid', '( r || E \\/ r || Z )')
    # case r || E
    C1 = '( %s /\\ r || E )' % CF
    f1 = mkst(w, C1)
    rinE = f1([f1([elre], 'a1i', '( r e. %s <-> ( r e. Prime /\\ r || E ) )' % PF('E')),
               f1([f1([rpr], 'adantr', 'r e. Prime'), f1([], 'simpr', 'r || E')], 'jca',
                  '( r e. Prime /\\ r || E )')], 'mpbird', 'r e. %s' % PF('E'))
    pfeF = sf([pfe], 'adantr', '%s = S' % PF('E'))
    pfe1 = f1([pfeF], 'adantr', '%s = S' % PF('E'))
    rS = f1([f1([pfe1], 'eleq2d', '( r e. %s <-> r e. S )' % PF('E')), rinE], 'mpbid', 'r e. S')
    c1 = f1([rS], 'orcd', '( r e. S \\/ r = Z )')
    # case r || Z
    C2 = '( %s /\\ r || Z )' % CF
    f2 = mkst(w, C2)
    ruz = f2([f2([rpr], 'adantr', 'r e. Prime'), w.inst('prmuz2')], 'syl', 'r e. ( ZZ>= ` 2 )')
    zF = sf([z], 'adantr', 'Z e. Prime')
    dp = f2([ruz, f2([zF], 'adantr', 'Z e. Prime'), w.inst('dvdsprm')], 'syl2anc',
            '( r || Z <-> r = Z )')
    rz = f2([dp, f2([], 'simpr', 'r || Z')], 'mpbid', 'r = Z')
    c2 = f2([rz], 'olcd', '( r e. S \\/ r = Z )')
    fwd0 = sf([c1, c2, dis], 'mpjaodan', '( r e. S \\/ r = Z )')
    fwd = sf([sf([w.s([], 'elun', '( r e. ( S u. { Z } ) <-> ( r e. S \\/ r e. { Z } ) )')], 'a1i',
                 '( r e. ( S u. { Z } ) <-> ( r e. S \\/ r e. { Z } ) )'),
              sf([sf([w.s([], 'elsn', '( r e. { Z } <-> r = Z )')], 'a1i',
                     '( r e. { Z } <-> r = Z )')], 'orbi2d',
                 '( ( r e. S \\/ r e. { Z } ) <-> ( r e. S \\/ r = Z ) )')], 'bitrd',
             '( r e. ( S u. { Z } ) <-> ( r e. S \\/ r = Z ) )')
    fwd2 = sf([fwd, fwd0], 'mpbird', 'r e. ( S u. { Z } )')
    # backward
    CB = '( %s /\\ r e. ( S u. { Z } ) )' % A
    sb = mkst(w, CB)
    rinu = sb([], 'simpr', 'r e. ( S u. { Z } )')
    disb = sb([sb([w.s([], 'elun', '( r e. ( S u. { Z } ) <-> ( r e. S \\/ r e. { Z } ) )')], 'a1i',
                  '( r e. ( S u. { Z } ) <-> ( r e. S \\/ r e. { Z } ) )'), rinu], 'mpbid',
              '( r e. S \\/ r e. { Z } )')
    B1 = '( %s /\\ r e. S )' % CB
    g1 = mkst(w, B1)
    pfeB = sb([pfe], 'adantr', '%s = S' % PF('E'))
    ezB = sb([ez], 'adantr', 'E e. ZZ')
    zzB = sb([zz], 'adantr', 'Z e. ZZ')
    eznzB = sb([eznz], 'adantr', '%s e. ZZ' % EZ)
    zB = sb([z], 'adantr', 'Z e. Prime')
    rpfE = g1([g1([g1([pfeB], 'adantr', '%s = S' % PF('E'))], 'eleq2d',
                  '( r e. %s <-> r e. S )' % PF('E')), g1([], 'simpr', 'r e. S')], 'mpbird',
              'r e. %s' % PF('E'))
    rpe = g1([g1([elre], 'a1i', '( r e. %s <-> ( r e. Prime /\\ r || E ) )' % PF('E')), rpfE],
             'mpbid', '( r e. Prime /\\ r || E )')
    rprb = g1([rpe], 'simpld', 'r e. Prime')
    rdvb = g1([rpe], 'simprd', 'r || E')
    rz1 = g1([rprb, w.inst('prmz')], 'syl', 'r e. ZZ')
    ez1 = g1([ezB], 'adantr', 'E e. ZZ')
    zz1 = g1([zzB], 'adantr', 'Z e. ZZ')
    edvez = g1([ez1, zz1, w.inst('dvdsmul1')], 'syl2anc', 'E || %s' % EZ)
    eznz1 = g1([eznzB], 'adantr', '%s e. ZZ' % EZ)
    tr = g1([rz1, ez1, eznz1, w.inst('dvdstr')], 'syl3anc',
            '( ( r || E /\\ E || %s ) -> r || %s )' % (EZ, EZ))
    rdvez = g1([g1([rdvb, edvez], 'jca', '( r || E /\\ E || %s )' % EZ), tr], 'mpd',
               'r || %s' % EZ)
    b1 = g1([g1([elrz], 'a1i', '( r e. %s <-> ( r e. Prime /\\ r || %s ) )' % (PF(EZ), EZ)),
             g1([rprb, rdvez], 'jca', '( r e. Prime /\\ r || %s )' % EZ)], 'mpbird',
            'r e. %s' % PF(EZ))
    B2 = '( %s /\\ r e. { Z } )' % CB
    g2 = mkst(w, B2)
    rzeq = g2([g2([], 'simpr', 'r e. { Z }'), w.inst('elsni')], 'syl', 'r = Z')
    zdvez = g2([g2([ezB], 'adantr', 'E e. ZZ'), g2([zzB], 'adantr', 'Z e. ZZ'),
                w.inst('dvdsmul2')], 'syl2anc', 'Z || %s' % EZ)
    zprb = g2([zB], 'adantr', 'Z e. Prime')
    subz = w.s([], 'eleq1', '( r = Z -> ( r e. %s <-> Z e. %s ) )' % (PF(EZ), PF(EZ)))
    zinz = g2([g2([w.s([w.s([], 'breq1', '( q = Z -> ( q || %s <-> Z || %s ) )' % (EZ, EZ))], 'elrab',
                      '( Z e. %s <-> ( Z e. Prime /\\ Z || %s ) )' % (PF(EZ), EZ))], 'a1i',
                  '( Z e. %s <-> ( Z e. Prime /\\ Z || %s ) )' % (PF(EZ), EZ)),
               g2([zprb, zdvez], 'jca', '( Z e. Prime /\\ Z || %s )' % EZ)], 'mpbird',
              'Z e. %s' % PF(EZ))
    b2 = g2([rzeq, zinz], 'eqeltrd', 'r e. %s' % PF(EZ))
    bwd = sb([b1, b2, disb], 'mpjaodan', 'r e. %s' % PF(EZ))
    bi = st([w.s([fwd2], 'ex', '( %s -> ( r e. %s -> r e. ( S u. { Z } ) ) )' % (A, PF(EZ))),
             w.s([bwd], 'ex', '( %s -> ( r e. ( S u. { Z } ) -> r e. %s ) )' % (A, PF(EZ)))],
            'impbid', '( r e. %s <-> r e. ( S u. { Z } ) )' % PF(EZ))
    seteq = st([bi], 'eqrdv', '%s = ( S u. { Z } )' % PF(EZ))
    w.qed([st([ezn, sqez], 'jca', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (EZ, EZ)), seteq], 'jca',
          '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = ( S u. { Z } ) ) )'
          % (A, EZ, EZ, PF(EZ)))
    return w


def PRD(X): return 'prod_ p e. %s p' % X


def PHIS(X):
    return ('( %s C_ Prime -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) )'
            % (X, PRD(X), PRD(X), PF(PRD(X)), X))


def sqfprod():
    w = W('sqfprod',
          'The product of a finite set of primes is a squarefree positive integer whose prime '
          'divisors are exactly that set.')
    YZ = '( y u. { z } )'
    def subst(X):
        e = 'x = %s' % X
        pe = w.s([], 'prodeq1', '( %s -> %s = %s )' % (e, PRD('x'), PRD(X)))
        a = w.s([pe], 'eleq1d', '( %s -> ( %s e. NN <-> %s e. NN ) )' % (e, PRD('x'), PRD(X)))
        b0 = w.s([pe], 'fveq2d', '( %s -> ( mmu ` %s ) = ( mmu ` %s ) )' % (e, PRD('x'), PRD(X)))
        b = w.s([b0], 'neeq1d',
                '( %s -> ( ( mmu ` %s ) =/= 0 <-> ( mmu ` %s ) =/= 0 ) )' % (e, PRD('x'), PRD(X)))
        ab = w.s([a, b], 'anbi12d',
                 '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) <-> ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) ) )'
                 % (e, PRD('x'), PRD('x'), PRD(X), PRD(X)))
        c0 = w.s([pe], 'breq2d', '( %s -> ( q || %s <-> q || %s ) )' % (e, PRD('x'), PRD(X)))
        c1 = w.s([c0], 'rabbidv', '( %s -> %s = %s )' % (e, PF(PRD('x')), PF(PRD(X))))
        cid = w.s([], 'id', '( %s -> x = %s )' % (e, X))
        c = w.s([c1, cid], 'eqeq12d',
                '( %s -> ( %s = x <-> %s = %s ) )' % (e, PF(PRD('x')), PF(PRD(X)), X))
        abc = w.s([ab, c], 'anbi12d',
                  '( %s -> ( ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = x ) <-> '
                  '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) ) )'
                  % (e, PRD('x'), PRD('x'), PF(PRD('x')), PRD(X), PRD(X), PF(PRD(X)), X))
        ss = w.s([], 'sseq1', '( %s -> ( x C_ Prime <-> %s C_ Prime ) )' % (e, X))
        return w.s([ss, abc], 'imbi12d', '( %s -> ( %s <-> %s ) )' % (e, PHIS('x'), PHIS(X)))
    h1 = subst('(/)')
    h2 = subst('y')
    h3 = subst(YZ)
    h4 = subst('T')
    # base case
    p0 = w.s([], 'prod0', '%s = 1' % PRD('(/)'))
    n1 = w.s([], '1nn', '1 e. NN')
    b1 = w.s([p0, n1], 'eqeltri', '%s e. NN' % PRD('(/)'))
    s1 = w.s([p0], 'fveq2i', '( mmu ` %s ) = ( mmu ` 1 )' % PRD('(/)'))
    s2 = w.s([s1, w.s([], 'sqf1', '( mmu ` 1 ) =/= 0')], 'eqnetri', '( mmu ` %s ) =/= 0' % PRD('(/)'))
    rgen = w.s([w.s([], 'nprmdvds1', '( q e. Prime -> -. q || 1 )')], 'rgen',
               'A. q e. Prime -. q || 1')
    rab = w.s([w.s([], 'rabeq0', '( %s = (/) <-> A. q e. Prime -. q || 1 )' % PF('1')), rgen],
              'mpbir', '%s = (/)' % PF('1'))
    c0 = w.s([p0], 'breq2i', '( q || %s <-> q || 1 )' % PRD('(/)'))
    c1 = w.s([c0], 'rabbii', '%s = %s' % (PF(PRD('(/)')), PF('1')))
    c2 = w.s([c1, rab], 'eqtri', '%s = (/)' % PF(PRD('(/)')))
    base = w.s([w.s([b1, s2], 'pm3.2i', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PRD('(/)'), PRD('(/)'))),
                c2], 'pm3.2i',
               '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = (/) )'
               % (PRD('(/)'), PRD('(/)'), PF(PRD('(/)'))))
    h5 = w.s([base], 'a1i', PHIS('(/)'))
    # the step
    AST = '( y e. Fin /\\ -. z e. y )'
    CS = '( %s /\\ %s C_ Prime )' % (AST, YZ)
    st = mkst(w, CS)
    yfin = st([], 'simpll', 'y e. Fin')
    nz = st([], 'simplr', '-. z e. y')
    ssp = st([], 'simpr', '%s C_ Prime' % YZ)
    ysyz = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    ysP = st([ysyz, ssp], 'sstrd', 'y C_ Prime')
    zyz = st([w.s([], 'ssun2', '{ z } C_ %s' % YZ),
              st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')], 'sselid', 'z e. %s' % YZ)
    zP = st([ssp, zyz], 'sseldd', 'z e. Prime')
    zn = st([zP, w.inst('prmnn')], 'syl', 'z e. NN')
    zc = st([zn], 'nncnd', 'z e. CC')
    # the product splits off z
    nfd = w.s([], 'nfcv', 'F/_ p z')
    zex = st([w.s([], 'vex', 'z e. _V')], 'a1i', 'z e. _V')
    BY = '( %s /\\ p e. y )' % CS
    fy = mkst(w, BY)
    pP = fy([fy([ysP], 'adantr', 'y C_ Prime'), fy([], 'simpr', 'p e. y')], 'sseldd', 'p e. Prime')
    pc = fy([fy([pP, w.inst('prmnn')], 'syl', 'p e. NN')], 'nncnd', 'p e. CC')
    idp = w.s([], 'id', '( p = z -> p = z )')
    spl = st([nfd, yfin, zex, nz, pc, idp, zc], 'fprodsplitsn',
             '%s = ( %s x. z )' % (PRD(YZ), PRD('y')))
    # the step: apply sqfmul with E = the product over y, S = y, Z = z
    CI = '( %s /\\ %s )' % (CS, PHIS('y'))
    si = mkst(w, CI)
    ph_y = si([], 'simpr', PHIS('y'))
    ysP2 = si([ysP], 'adantr', 'y C_ Prime')
    facts = si([ph_y, ysP2], 'mpd',
               '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = y )'
               % (PRD('y'), PRD('y'), PF(PRD('y'))))
    f12 = si([facts], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PRD('y'), PRD('y')))
    f1 = si([f12], 'simpld', '%s e. NN' % PRD('y'))
    f2 = si([f12], 'simprd', '( mmu ` %s ) =/= 0' % PRD('y'))
    f3 = si([facts], 'simprd', '%s = y' % PF(PRD('y')))
    zP2 = si([zP], 'adantr', 'z e. Prime')
    nz2 = si([nz], 'adantr', '-. z e. y')
    mul = si([si([f1, f2, f3], '3jca',
                 '( %s e. NN /\\ ( mmu ` %s ) =/= 0 /\\ %s = y )'
                 % (PRD('y'), PRD('y'), PF(PRD('y')))),
              si([zP2, nz2], 'jca', '( z e. Prime /\\ -. z e. y )'), w.inst('sqfmul')], 'syl2anc',
             '( ( ( %s x. z ) e. NN /\\ ( mmu ` ( %s x. z ) ) =/= 0 ) /\\ %s = %s )'
             % (PRD('y'), PRD('y'), PF('( %s x. z )' % PRD('y')), YZ))
    # transport along the product identity
    spl2 = si([spl], 'adantr', '%s = ( %s x. z )' % (PRD(YZ), PRD('y')))
    m1 = si([mul], 'simpld', '( ( %s x. z ) e. NN /\\ ( mmu ` ( %s x. z ) ) =/= 0 )'
            % (PRD('y'), PRD('y')))
    m1a = si([m1], 'simpld', '( %s x. z ) e. NN' % PRD('y'))
    m1b = si([m1], 'simprd', '( mmu ` ( %s x. z ) ) =/= 0' % PRD('y'))
    m2 = si([mul], 'simprd', '%s = %s' % (PF('( %s x. z )' % PRD('y')), YZ))
    t1 = si([spl2, m1a], 'eqeltrd', '%s e. NN' % PRD(YZ))
    t2 = si([si([spl2], 'fveq2d', '( mmu ` %s ) = ( mmu ` ( %s x. z ) )' % (PRD(YZ), PRD('y'))), m1b],
            'eqnetrd', '( mmu ` %s ) =/= 0' % PRD(YZ))
    t3a0 = st([st([spl], 'breq2d', '( q || %s <-> q || ( %s x. z ) )' % (PRD(YZ), PRD('y')))],
              'rabbidv', '%s = %s' % (PF(PRD(YZ)), PF('( %s x. z )' % PRD('y'))))
    t3a = si([t3a0], 'adantr', '%s = %s' % (PF(PRD(YZ)), PF('( %s x. z )' % PRD('y'))))
    t3 = si([t3a, m2], 'eqtrd', '%s = %s' % (PF(PRD(YZ)), YZ))
    concl = si([si([t1, t2], 'jca', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PRD(YZ), PRD(YZ))), t3],
               'jca', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )'
               % (PRD(YZ), PRD(YZ), PF(PRD(YZ)), YZ))
    ex1 = w.s([concl], 'ex', '( %s -> ( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) ) )'
              % (CS, PHIS('y'), PRD(YZ), PRD(YZ), PF(PRD(YZ)), YZ))
    ex2 = w.s([ex1], 'com12', '( %s -> ( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) ) )'
              % (PHIS('y'), CS, PRD(YZ), PRD(YZ), PF(PRD(YZ)), YZ))
    ex3 = w.s([ex2], 'expd',
              '( %s -> ( %s -> ( %s C_ Prime -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) ) ) )'
              % (PHIS('y'), AST, YZ, PRD(YZ), PRD(YZ), PF(PRD(YZ)), YZ))
    h6 = w.s([ex3], 'com12', '( %s -> ( %s -> %s ) )' % (AST, PHIS('y'), PHIS(YZ)))
    res = w.s([h1, h2, h3, h4, h5, h6], 'findcard2s', '( T e. Fin -> %s )' % PHIS('T'))
    w.qed([res], 'imp',
          '( ( T e. Fin /\\ T C_ Prime ) -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = T ) )'
          % (PRD('T'), PRD('T'), PF(PRD('T'))))
    return w


def sqfprodid():
    w = W('sqfprodid', 'A squarefree positive integer is the product of its prime divisors.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    TR = PF('D', 'r')
    PR = PRD(TR)
    TD = PF('D')
    PD = PRD(TD)
    st = mkst(w, A)
    d = st([], 'simpl', 'D e. NN')
    sq = st([], 'simpr', '( mmu ` D ) =/= 0')
    finp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), TR))], 'a1i',
             '%s = %s' % (PF('D', 'p'), TR))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % TR)
    ssp = st([w.s([], 'ssrab2', '%s C_ Prime' % TR)], 'a1i', '%s C_ Prime' % TR)
    sp = st([fin, ssp, w.inst('sqfprod')], 'syl2anc',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )' % (PR, PR, PF(PR), TR))
    p12 = st([sp], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PR, PR))
    pnn = st([p12], 'simpld', '%s e. NN' % PR)
    psq = st([p12], 'simprd', '( mmu ` %s ) =/= 0' % PR)
    pset = st([sp], 'simprd', '%s = %s' % (PF(PR), TR))
    # A. s e. Prime ( s || PR <-> s || D )
    BS = '( %s /\\ s e. Prime )' % A
    fs = mkst(w, BS)
    sp2 = fs([], 'simpr', 's e. Prime')
    elP = w.s([w.s([], 'breq1', '( q = s -> ( q || %s <-> s || %s ) )' % (PR, PR))], 'elrab',
              '( s e. %s <-> ( s e. Prime /\\ s || %s ) )' % (PF(PR), PR))
    elD = w.s([w.s([], 'breq1', '( r = s -> ( r || D <-> s || D ) )')], 'elrab',
              '( s e. %s <-> ( s e. Prime /\\ s || D ) )' % TR)
    eqr = fs([fs([pset], 'adantr', '%s = %s' % (PF(PR), TR))], 'eleq2d',
             '( s e. %s <-> s e. %s )' % (PF(PR), TR))
    b1 = fs([fs([elP], 'a1i', '( s e. %s <-> ( s e. Prime /\\ s || %s ) )' % (PF(PR), PR)), eqr],
            'bitr3d', '( ( s e. Prime /\\ s || %s ) <-> s e. %s )' % (PR, TR))
    b2 = fs([b1, fs([elD], 'a1i', '( s e. %s <-> ( s e. Prime /\\ s || D ) )' % TR)], 'bitrd',
            '( ( s e. Prime /\\ s || %s ) <-> ( s e. Prime /\\ s || D ) )' % PR)
    bfin = fs([fs([sp2], 'biantrurd', '( s || %s <-> ( s e. Prime /\\ s || %s ) )' % (PR, PR)),
               fs([b2, fs([sp2], 'biantrurd', '( s || D <-> ( s e. Prime /\\ s || D ) )')], 'bitr4d',
                  '( ( s e. Prime /\\ s || %s ) <-> s || D )' % PR)], 'bitrd',
              '( s || %s <-> s || D )' % PR)
    ral = st([bfin], 'ralrimiva', 'A. s e. Prime ( s || %s <-> s || D )' % PR)
    s11 = st([st([pnn, psq], 'jca', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PR, PR)),
              st([d, sq], 'jca', A), w.inst('sqf11')], 'syl2anc',
             '( %s = D <-> A. s e. Prime ( s || %s <-> s || D ) )' % (PR, PR))
    eqD = st([s11, ral], 'mpbird', '%s = D' % PR)
    cbv2 = st([w.s([], 'cbvrabv', '%s = %s' % (TD, TR))], 'a1i', '%s = %s' % (TD, TR))
    pq = st([cbv2], 'prodeq1d', '%s = %s' % (PD, PR))
    w.qed([pq, eqD], 'eqtrd', '( %s -> %s = D )' % (A, PD))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['sqfmul']:
        globals()[f]().run()
