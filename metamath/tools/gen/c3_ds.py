"""Sortie C3 section 5: the Dirichlet series on the half-plane Re > 1."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

RZ = '( Re ` Z )'
FN = '( n e. NN |-> ( n ^c -u T ) )'
HN = '( n e. NN |-> ( C x. ( n ^c -u T ) ) )'
NU1 = '( ZZ>= ` 1 )'

# ---- zsercvgc --------------------------------------------------------------
w = W('zsercvgc', 'A constant multiple of the zeta series converges for a real abscissa above one.')
A0 = '( ( T e. RR /\\ 1 < T ) /\\ C e. CC )'
An = '( %s /\\ k e. NN )' % A0
tt = w.s([], 'simpl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
cc = w.s([], 'simpr', '( %s -> C e. CC )' % A0)
ntr = w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A0)
nu1 = w.s([], 'nnuz', 'NN = %s' % NU1)
kn = w.s([], 'simpr', '( %s -> k e. NN )' % An)
subf = w.s([], 'oveq1', '( n = k -> ( n ^c -u T ) = ( k ^c -u T ) )')
vf = mpv(w, An, FN, 'k', '( k ^c -u T )', subf, kn, vexd(w, An, '( k ^c -u T )'))
kcl = w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % An), w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % An)],
          'rpcxpcld', '( %s -> ( k ^c -u T ) e. RR+ )' % An)
kcc = w.s([kcl], 'rpcnd', '( %s -> ( k ^c -u T ) e. CC )' % An)
fcc = w.s([vf, kcc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (An, FN))
subh = w.s([subf], 'oveq2d', '( n = k -> ( C x. ( n ^c -u T ) ) = ( C x. ( k ^c -u T ) ) )')
vh = mpv(w, An, HN, 'k', '( C x. ( k ^c -u T ) )', subh, kn, vexd(w, An, '( C x. ( k ^c -u T ) )'))
vh2 = w.s([vh, w.s([w.s([vf], 'eqcomd', '( %s -> ( k ^c -u T ) = ( %s ` k ) )' % (An, FN))], 'oveq2d',
                   '( %s -> ( C x. ( k ^c -u T ) ) = ( C x. ( %s ` k ) ) )' % (An, FN))], 'eqtrd',
          '( %s -> ( %s ` k ) = ( C x. ( %s ` k ) ) )' % (An, HN, FN))
SQ = 'seq 1 ( + , %s )' % FN
cv = w.s([tt, w.inst('zsercvg')], 'syl', '( %s -> %s e. dom ~~> )' % (A0, SQ))
lim = w.s([cv, w.s([w.s([], 'climdm', '( %s e. dom ~~> <-> %s ~~> ( ~~> ` %s ) )' % (SQ, SQ, SQ))], 'a1i',
                   '( %s -> ( %s e. dom ~~> <-> %s ~~> ( ~~> ` %s ) ) )' % (A0, SQ, SQ, SQ))], 'mpbid',
          '( %s -> %s ~~> ( ~~> ` %s ) )' % (A0, SQ, SQ))
mul = w.s([nu1, z1, cc, lim, fcc, vh2], 'isermulc2',
          '( %s -> seq 1 ( + , %s ) ~~> ( C x. ( ~~> ` %s ) ) )' % (A0, HN, SQ))
w.qed([w.s([w.s([], 'climrel', 'Rel ~~>')], 'a1i', '( %s -> Rel ~~> )' % A0), mul, w.inst('releldm')], 'syl2anc',
      '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HN)); run3(w)

# ---- cfb0 ------------------------------------------------------------------
w = W('cfb0', 'A bound on the modulus of the coefficients of a Dirichlet series is nonnegative.')
A0 = CFB
af = w.s([], 'simp1', '( %s -> A : NN --> CC )' % A0)
cr = w.s([], 'simp2', '( %s -> C e. RR )' % A0)
ral = w.s([], 'simp3', '( %s -> A. m e. NN ( abs ` ( A ` m ) ) <_ C )' % A0)
n1 = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0)
e1 = w.s([], 'fveq2', '( m = 1 -> ( A ` m ) = ( A ` 1 ) )')
e2 = w.s([e1], 'fveq2d', '( m = 1 -> ( abs ` ( A ` m ) ) = ( abs ` ( A ` 1 ) ) )')
e3 = w.s([e2], 'breq1d', '( m = 1 -> ( ( abs ` ( A ` m ) ) <_ C <-> ( abs ` ( A ` 1 ) ) <_ C ) )')
le = w.s([e3, ral, n1], 'rspcdva', '( %s -> ( abs ` ( A ` 1 ) ) <_ C )' % A0)
a1 = w.s([af, n1], 'ffvelcdmd', '( %s -> ( A ` 1 ) e. CC )' % A0)
w.qed([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0),
       w.s([a1], 'abscld', '( %s -> ( abs ` ( A ` 1 ) ) e. RR )' % A0), cr,
       w.s([a1], 'absge0d', '( %s -> 0 <_ ( abs ` ( A ` 1 ) ) )' % A0), le], 'letrd',
      '( %s -> 0 <_ C )' % A0); run3(w)

# ---------------------------------------------------------------------------
# the general Dirichlet series on Re > 1
RZ = '( Re ` Z )'
TRM = '( ( A ` n ) x. ( n ^c -u Z ) )'
GN = '( n e. NN |-> %s )' % TRM
ABN = '( n e. NN |-> ( abs ` %s ) )' % TRM
HNZ = '( n e. NN |-> ( C x. ( n ^c -u %s ) ) )' % RZ
FNZ = '( n e. NN |-> ( n ^c -u %s ) )' % RZ
TRMK = '( ( A ` k ) x. ( k ^c -u Z ) )'
DSH = '( %s /\\ ( Z e. CC /\\ 1 < %s ) )' % (CFB, RZ)


def base(w, A0, dsh=None):
    d = {}
    if dsh is None:
        d['cfb'] = cfb = w.s([], 'simpl', '( %s -> %s )' % (A0, CFB))
    else:
        d['dsh'] = dsh
        d['cfb'] = cfb = w.s([dsh, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
    d['af'] = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
    d['cr'] = w.s([cfb, w.inst('simp2')], 'syl', '( %s -> C e. RR )' % A0)
    d['ral'] = w.s([cfb, w.inst('simp3')], 'syl', '( %s -> A. m e. NN ( abs ` ( A ` m ) ) <_ C )' % A0)
    d['c0'] = w.s([cfb, w.inst('cfb0')], 'syl', '( %s -> 0 <_ C )' % A0)
    if dsh is None:
        d['zc'] = zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
        d['zgt'] = w.s([], 'simprr', '( %s -> 1 < %s )' % (A0, RZ))
    else:
        d['zc'] = zc = w.s([dsh, w.inst('simprl')], 'syl', '( %s -> Z e. CC )' % A0)
        d['zgt'] = w.s([dsh, w.inst('simprr')], 'syl', '( %s -> 1 < %s )' % (A0, RZ))
    d['rz'] = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
    d['nu1'] = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    d['z1'] = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A0)
    d['n1'] = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0)
    return d


def terms(w, A0, d, mem='NN'):
    """the termwise steps under ( A0 /\\ k e. mem )"""
    Ak = '( %s /\\ k e. %s )' % (A0, mem)
    t = {'ante': Ak}
    if mem == 'NN':
        kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    else:
        kn = w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, mem)),
                  w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i',
                      '( %s -> ( ZZ>= ` 1 ) = NN )' % Ak)], 'eleqtrd', '( %s -> k e. NN )' % Ak)
    t['kn'] = kn
    ak = w.s([w.s([d['af']], 'adantr', '( %s -> A : NN --> CC )' % Ak), kn], 'ffvelcdmd',
             '( %s -> ( A ` k ) e. CC )' % Ak)
    t['ak'] = ak
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    t['krp'] = krp
    nzc = w.s([w.s([w.s([d['zc']], 'negcld', '( %s -> -u Z e. CC )' % A0)], 'adantr', '( %s -> -u Z e. CC )' % Ak)],
              'idi', '( %s -> -u Z e. CC )' % Ak)
    pz = w.s([w.s([krp], 'rpcnd', '( %s -> k e. CC )' % Ak), nzc, w.inst('cxpcl')], 'syl2anc',
             '( %s -> ( k ^c -u Z ) e. CC )' % Ak)
    trmc = w.s([ak, pz], 'mulcld', '( %s -> %s e. CC )' % (Ak, TRMK))
    t['trmc'] = trmc
    sub1 = w.s([], 'fveq2', '( n = k -> ( A ` n ) = ( A ` k ) )')
    sub2 = w.s([], 'oveq1', '( n = k -> ( n ^c -u Z ) = ( k ^c -u Z ) )')
    subg = w.s([sub1, sub2], 'oveq12d', '( n = k -> %s = %s )' % (TRM, TRMK))
    t['vG'] = mpv(w, Ak, GN, 'k', TRMK, subg, kn, vexd(w, Ak, TRMK))
    suba = w.s([subg], 'fveq2d', '( n = k -> ( abs ` %s ) = ( abs ` %s ) )' % (TRM, TRMK))
    t['vAB'] = mpv(w, Ak, ABN, 'k', '( abs ` %s )' % TRMK, suba, kn, vexd(w, Ak, '( abs ` %s )' % TRMK, 'fv'))
    nrz = w.s([w.s([w.s([d['rz']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))], 'adantr',
                   '( %s -> -u %s e. RR )' % (Ak, RZ))], 'idi', '( %s -> -u %s e. RR )' % (Ak, RZ))
    prp = w.s([krp, nrz], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, RZ))
    t['prp'] = prp
    subf = w.s([], 'oveq1', '( n = k -> ( n ^c -u %s ) = ( k ^c -u %s ) )' % (RZ, RZ))
    t['vF'] = mpv(w, Ak, FNZ, 'k', '( k ^c -u %s )' % RZ, subf, kn, vexd(w, Ak, '( k ^c -u %s )' % RZ))
    subh = w.s([subf], 'oveq2d', '( n = k -> ( C x. ( n ^c -u %s ) ) = ( C x. ( k ^c -u %s ) ) )' % (RZ, RZ))
    t['vH'] = mpv(w, Ak, HNZ, 'k', '( C x. ( k ^c -u %s ) )' % RZ, subh, kn,
                  vexd(w, Ak, '( C x. ( k ^c -u %s ) )' % RZ))
    # the termwise bound
    rzk = w.s([d['rz']], 'adantr', '( %s -> %s e. RR )' % (Ak, RZ))
    t['bnd'] = w.s([w.s([w.s([d['cfb']], 'adantr', '( %s -> %s )' % (Ak, CFB)),
                         w.s([w.s([kn, rzk, w.s([d['zc']], 'adantr', '( %s -> Z e. CC )' % Ak)], '3jca',
                                  '( %s -> ( k e. NN /\\ %s e. RR /\\ Z e. CC ) )' % (Ak, RZ)),
                              w.s([rzk], 'leidd', '( %s -> %s <_ %s )' % (Ak, RZ, RZ))], 'jca',
                             '( %s -> ( ( k e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) )' % (Ak, RZ, RZ, RZ))],
                        'jca', '( %s -> ( %s /\\ ( ( k e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) ) )' % (Ak, CFB, RZ, RZ, RZ)),
                    w.inst('dtmabs')], 'syl',
                   '( %s -> ( abs ` %s ) <_ ( C x. ( k ^c -u %s ) ) )' % (Ak, TRMK, RZ))
    t['crk'] = w.s([d['cr']], 'adantr', '( %s -> C e. RR )' % Ak)
    return t


# ---- dsercvg ---------------------------------------------------------------
w = W('dsercvg', 'A Dirichlet series with bounded coefficients converges to the right of the line one.')
A0 = DSH
d = base(w, A0)
t = terms(w, A0, d)
tu = terms(w, A0, d, '( ZZ>= ` 1 )')
Ak, Au = t['ante'], tu['ante']
mj = w.s([w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
               w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0)], 'jca',
              '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ C e. CC ) )' % (A0, RZ, RZ)), w.inst('zsercvgc')], 'syl',
         '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HNZ))
hre = w.s([t['vH'], w.s([t['crk'], w.s([t['prp']], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))],
                        'remulcld', '( %s -> ( C x. ( k ^c -u %s ) ) e. RR )' % (Ak, RZ))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. RR )' % (Ak, HNZ))
are = w.s([t['vAB'], w.s([t['trmc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, TRMK))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. RR )' % (Ak, ABN))
ag0 = w.s([w.s([tu['trmc']], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Au, TRMK)), tu['vAB']], 'breqtrrd',
          '( %s -> 0 <_ ( %s ` k ) )' % (Au, ABN))
alh = w.s([w.s([tu['vAB'], tu['bnd']], 'eqbrtrd',
                '( %s -> ( %s ` k ) <_ ( C x. ( k ^c -u %s ) ) )' % (Au, ABN, RZ)), tu['vH']], 'breqtrrd',
          '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Au, ABN, HNZ))
abcv = w.s([d['nu1'], d['n1'], hre, are, mj, ag0, alh], 'cvgcmp',
           '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, ABN))
abv = w.s([t['vAB'], w.s([t['vG']], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, GN, TRMK))],
          'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, ABN, GN))
gcc = w.s([t['vG'], t['trmc']], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, GN))
w.qed([d['nu1'], d['z1'], abv, gcc, abcv], 'abscvgcvg',
      '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GN)); run3(w)

# ---- dserabcvg -------------------------------------------------------------
w = W('dserabcvg', 'A Dirichlet series with bounded coefficients converges absolutely to the right of the line one.')
A0 = DSH
d = base(w, A0)
t = terms(w, A0, d)
tu = terms(w, A0, d, '( ZZ>= ` 1 )')
Ak, Au = t['ante'], tu['ante']
mj = w.s([w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
               w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0)], 'jca',
              '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ C e. CC ) )' % (A0, RZ, RZ)), w.inst('zsercvgc')], 'syl',
         '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HNZ))
hre = w.s([t['vH'], w.s([t['crk'], w.s([t['prp']], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))],
                        'remulcld', '( %s -> ( C x. ( k ^c -u %s ) ) e. RR )' % (Ak, RZ))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. RR )' % (Ak, HNZ))
are = w.s([t['vAB'], w.s([t['trmc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, TRMK))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. RR )' % (Ak, ABN))
ag0 = w.s([w.s([tu['trmc']], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Au, TRMK)), tu['vAB']], 'breqtrrd',
          '( %s -> 0 <_ ( %s ` k ) )' % (Au, ABN))
alh = w.s([w.s([tu['vAB'], tu['bnd']], 'eqbrtrd',
                '( %s -> ( %s ` k ) <_ ( C x. ( k ^c -u %s ) ) )' % (Au, ABN, RZ)), tu['vH']], 'breqtrrd',
          '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Au, ABN, HNZ))
w.qed([d['nu1'], d['n1'], hre, are, mj, ag0, alh], 'cvgcmp',
      '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, ABN)); run3(w)

# ---- dsercl ----------------------------------------------------------------
w = W('dsercl', 'A Dirichlet series with bounded coefficients is a complex number to the right of the line one.')
A0 = DSH
d = base(w, A0)
t = terms(w, A0, d)
Ak = t['ante']
cv = w.s([], 'dsercvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GN))
w.qed([d['nu1'], d['z1'], t['vG'], t['trmc'], cv], 'isumcl',
      '( %s -> sum_ k e. NN %s e. CC )' % (A0, TRMK)); run3(w)

# ---- dserabs ---------------------------------------------------------------
w = W('dserabs', 'The modulus of a Dirichlet series is below the series of the moduli.')
A0 = DSH
d = base(w, A0)
t = terms(w, A0, d)
Ak = t['ante']
gcc = w.s([t['vG'], t['trmc']], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, GN))
abv = w.s([t['vAB'], w.s([t['vG']], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, GN, TRMK))],
          'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, ABN, GN))
cv = w.s([], 'dsercvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GN))
cva = w.s([], 'dserabcvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, ABN))
lg = w.s([d['nu1'], d['z1'], t['vG'], t['trmc'], cv], 'isumclim2',
         '( %s -> seq 1 ( + , %s ) ~~> sum_ k e. NN %s )' % (A0, GN, TRMK))
abre = w.s([t['trmc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, TRMK))
la = w.s([d['nu1'], d['z1'], t['vAB'], w.s([abre], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, TRMK)), cva],
         'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> sum_ k e. NN ( abs ` %s ) )' % (A0, ABN, TRMK))
w.qed([d['nu1'], lg, la, d['z1'], gcc, abv], 'iserabs',
      '( %s -> ( abs ` sum_ k e. NN %s ) <_ sum_ k e. NN ( abs ` %s ) )' % (A0, TRMK, TRMK)); run3(w)

# ---- dserbnd ---------------------------------------------------------------
w = W('dserbnd', 'The Dirichlet-series bound to the right of the line one: the coefficient bound times one plus the reciprocal of the distance to the line.')
A0 = DSH
d = base(w, A0)
t = terms(w, A0, d)
Ak = t['ante']
cva = w.s([], 'dserabcvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, ABN))
mj = w.s([w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
               w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0)], 'jca',
              '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ C e. CC ) )' % (A0, RZ, RZ)), w.inst('zsercvgc')], 'syl',
         '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HNZ))
abre = w.s([t['trmc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, TRMK))
prre = w.s([t['prp']], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))
hre = w.s([t['crk'], prre], 'remulcld', '( %s -> ( C x. ( k ^c -u %s ) ) e. RR )' % (Ak, RZ))
# sum of the moduli <_ sum of the majorant
le1 = w.s([d['nu1'], d['z1'], t['vAB'], abre, t['vH'], hre, t['bnd'], cva, mj], 'isumle',
          '( %s -> sum_ k e. NN ( abs ` %s ) <_ sum_ k e. NN ( C x. ( k ^c -u %s ) ) )' % (A0, TRMK, RZ))
# the majorant series is C times the zeta series
zcv = w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
           w.inst('zsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, FNZ))
mc = w.s([d['nu1'], d['z1'], w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0), t['vF'],
          w.s([t['prp']], 'rpcnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Ak, RZ)), zcv], 'isummulc2',
         '( %s -> ( C x. sum_ k e. NN ( k ^c -u %s ) ) = sum_ k e. NN ( C x. ( k ^c -u %s ) ) )' % (A0, RZ, RZ))
zb = w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
          w.inst('zserbnd')], 'syl',
         '( %s -> sum_ k e. NN ( k ^c -u %s ) <_ ( 1 + ( 1 / ( %s - 1 ) ) ) )' % (A0, RZ, RZ))
# closures for the final chain
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
tm1 = w.s([d['rz'], r1], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (A0, RZ))
tm1rp = w.s([tm1, w.s([d['zgt'], w.s([r1, d['rz']], 'posdifd', '( %s -> ( 1 < %s <-> 0 < ( %s - 1 ) ) )' % (A0, RZ, RZ))],
                      'mpbid', '( %s -> 0 < ( %s - 1 ) )' % (A0, RZ))], 'elrpd', '( %s -> ( %s - 1 ) e. RR+ )' % (A0, RZ))
bre = w.s([r1, w.s([w.s([tm1rp], 'rpreccld', '( %s -> ( 1 / ( %s - 1 ) ) e. RR+ )' % (A0, RZ))], 'rpred',
                   '( %s -> ( 1 / ( %s - 1 ) ) e. RR )' % (A0, RZ))], 'readdcld',
          '( %s -> ( 1 + ( 1 / ( %s - 1 ) ) ) e. RR )' % (A0, RZ))
zsre = w.s([d['nu1'], d['z1'], t['vF'], prre, zcv], 'isumrecl', '( %s -> sum_ k e. NN ( k ^c -u %s ) e. RR )' % (A0, RZ))
mul = w.s([w.s([zsre, bre, w.s([d['cr'], d['c0']], 'jca', '( %s -> ( C e. RR /\\ 0 <_ C ) )' % A0)], '3jca',
                '( %s -> ( sum_ k e. NN ( k ^c -u %s ) e. RR /\\ ( 1 + ( 1 / ( %s - 1 ) ) ) e. RR /\\ ( C e. RR /\\ 0 <_ C ) ) )' % (A0, RZ, RZ)),
           zb, w.inst('lemul2a')], 'syl2anc',
          '( %s -> ( C x. sum_ k e. NN ( k ^c -u %s ) ) <_ ( C x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) )' % (A0, RZ, RZ))
mul2 = w.s([w.s([mc], 'eqcomd', '( %s -> sum_ k e. NN ( C x. ( k ^c -u %s ) ) = ( C x. sum_ k e. NN ( k ^c -u %s ) ) )' % (A0, RZ, RZ)),
            mul], 'eqbrtrd',
           '( %s -> sum_ k e. NN ( C x. ( k ^c -u %s ) ) <_ ( C x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) )' % (A0, RZ, RZ))
absle = w.s([], 'dserabs', '( %s -> ( abs ` sum_ k e. NN %s ) <_ sum_ k e. NN ( abs ` %s ) )' % (A0, TRMK, TRMK))
# reals
absre = w.s([w.s([], 'dsercl', '( %s -> sum_ k e. NN %s e. CC )' % (A0, TRMK))], 'abscld',
            '( %s -> ( abs ` sum_ k e. NN %s ) e. RR )' % (A0, TRMK))
absum = w.s([d['nu1'], d['z1'], t['vAB'], abre, cva], 'isumrecl',
            '( %s -> sum_ k e. NN ( abs ` %s ) e. RR )' % (A0, TRMK))
msum = w.s([d['nu1'], d['z1'], t['vH'], hre, mj], 'isumrecl',
           '( %s -> sum_ k e. NN ( C x. ( k ^c -u %s ) ) e. RR )' % (A0, RZ))
cbre = w.s([d['cr'], bre], 'remulcld', '( %s -> ( C x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) e. RR )' % (A0, RZ))
st1 = w.s([absre, absum, msum, absle, le1], 'letrd',
          '( %s -> ( abs ` sum_ k e. NN %s ) <_ sum_ k e. NN ( C x. ( k ^c -u %s ) ) )' % (A0, TRMK, RZ))
w.qed([absre, msum, cbre, st1, mul2], 'letrd',
      '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( C x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) )' % (A0, TRMK, RZ)); run3(w)

# ---- dsertl ----------------------------------------------------------------
UZ = '( ZZ>= ` ( M + 1 ) )'
w = W('dsertl', 'The tail of a Dirichlet series with bounded coefficients, to the right of the line one.')
A0 = '( %s /\\ M e. NN )' % DSH
dsh = w.s([], 'simpl', '( %s -> %s )' % (A0, DSH))
d = base(w, A0, dsh)
mn = w.s([], 'simpr', '( %s -> M e. NN )' % A0)
m1n = w.s([mn, w.inst('peano2nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % A0)
m1z = w.s([m1n], 'nnzd', '( %s -> ( M + 1 ) e. ZZ )' % A0)
u1n = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqcomi', '( ZZ>= ` 1 ) = NN')
m1u = w.s([m1n, w.s([u1n], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'eleqtrrd',
          '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
uss = w.s([w.s([m1u, w.inst('uzss')], 'syl', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (A0, UZ)),
           w.s([w.s([u1n], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'idi',
               '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)], 'sseqtrd', '( %s -> %s C_ NN )' % (A0, UZ))
t = terms(w, A0, d)
Ak = t['ante']
# the same steps over the tail index set
Au = '( %s /\\ k e. %s )' % (A0, UZ)
knnu = w.s([w.s([uss], 'adantr', '( %s -> %s C_ NN )' % (Au, UZ)), w.s([], 'simpr', '( %s -> k e. %s )' % (Au, UZ))],
           'sseldd', '( %s -> k e. NN )' % Au)
tu = {}
akU = w.s([w.s([d['af']], 'adantr', '( %s -> A : NN --> CC )' % Au), knnu], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % Au)
krpU = w.s([knnu], 'nnrpd', '( %s -> k e. RR+ )' % Au)
nzU = w.s([w.s([w.s([d['zc']], 'negcld', '( %s -> -u Z e. CC )' % A0)], 'adantr', '( %s -> -u Z e. CC )' % Au)],
          'idi', '( %s -> -u Z e. CC )' % Au)
pzU = w.s([w.s([krpU], 'rpcnd', '( %s -> k e. CC )' % Au), nzU, w.inst('cxpcl')], 'syl2anc',
          '( %s -> ( k ^c -u Z ) e. CC )' % Au)
trmU = w.s([akU, pzU], 'mulcld', '( %s -> %s e. CC )' % (Au, TRMK))
sub1U = w.s([], 'fveq2', '( n = k -> ( A ` n ) = ( A ` k ) )')
sub2U = w.s([], 'oveq1', '( n = k -> ( n ^c -u Z ) = ( k ^c -u Z ) )')
subgU = w.s([sub1U, sub2U], 'oveq12d', '( n = k -> %s = %s )' % (TRM, TRMK))
vGU = mpv(w, Au, GN, 'k', TRMK, subgU, knnu, vexd(w, Au, TRMK))
subaU = w.s([subgU], 'fveq2d', '( n = k -> ( abs ` %s ) = ( abs ` %s ) )' % (TRM, TRMK))
vABU = mpv(w, Au, ABN, 'k', '( abs ` %s )' % TRMK, subaU, knnu, vexd(w, Au, '( abs ` %s )' % TRMK, 'fv'))
nrzU = w.s([w.s([w.s([d['rz']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))], 'adantr',
                '( %s -> -u %s e. RR )' % (Au, RZ))], 'idi', '( %s -> -u %s e. RR )' % (Au, RZ))
prpU = w.s([krpU, nrzU], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (Au, RZ))
subfU = w.s([], 'oveq1', '( n = k -> ( n ^c -u %s ) = ( k ^c -u %s ) )' % (RZ, RZ))
vFU = mpv(w, Au, FNZ, 'k', '( k ^c -u %s )' % RZ, subfU, knnu, vexd(w, Au, '( k ^c -u %s )' % RZ))
subhU = w.s([subfU], 'oveq2d', '( n = k -> ( C x. ( n ^c -u %s ) ) = ( C x. ( k ^c -u %s ) ) )' % (RZ, RZ))
vHU = mpv(w, Au, HNZ, 'k', '( C x. ( k ^c -u %s ) )' % RZ, subhU, knnu, vexd(w, Au, '( C x. ( k ^c -u %s ) )' % RZ))
rzU = w.s([d['rz']], 'adantr', '( %s -> %s e. RR )' % (Au, RZ))
bndU = w.s([w.s([w.s([d['cfb']], 'adantr', '( %s -> %s )' % (Au, CFB)),
                 w.s([w.s([knnu, rzU, w.s([d['zc']], 'adantr', '( %s -> Z e. CC )' % Au)], '3jca',
                          '( %s -> ( k e. NN /\\ %s e. RR /\\ Z e. CC ) )' % (Au, RZ)),
                      w.s([rzU], 'leidd', '( %s -> %s <_ %s )' % (Au, RZ, RZ))], 'jca',
                     '( %s -> ( ( k e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) )' % (Au, RZ, RZ, RZ))], 'jca',
                '( %s -> ( %s /\\ ( ( k e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) ) )' % (Au, CFB, RZ, RZ, RZ)),
            w.inst('dtmabs')], 'syl',
           '( %s -> ( abs ` %s ) <_ ( C x. ( k ^c -u %s ) ) )' % (Au, TRMK, RZ))
crU = w.s([d['cr']], 'adantr', '( %s -> C e. RR )' % Au)
# convergence on the tail
nu1 = d['nu1']
gcc = w.s([t['vG'], t['trmc']], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, GN))
abcc = w.s([t['vAB'], w.s([w.s([t['trmc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, TRMK))], 'recnd',
                          '( %s -> ( abs ` %s ) e. CC )' % (Ak, TRMK))], 'eqeltrd',
           '( %s -> ( %s ` k ) e. CC )' % (Ak, ABN))
hcc = w.s([t['vH'], w.s([w.s([t['crk'], w.s([t['prp']], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))],
                             'remulcld', '( %s -> ( C x. ( k ^c -u %s ) ) e. RR )' % (Ak, RZ))], 'recnd',
                        '( %s -> ( C x. ( k ^c -u %s ) ) e. CC )' % (Ak, RZ))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. CC )' % (Ak, HNZ))
cvg = w.s([dsh, w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GN))
cvga = w.s([dsh, w.inst('dserabcvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, ABN))
mjA = w.s([w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
                w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0)], 'jca',
               '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ C e. CC ) )' % (A0, RZ, RZ)), w.inst('zsercvgc')], 'syl',
          '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HNZ))
cvgu = w.s([cvg, w.s([nu1, m1n, gcc], 'iserex',
                     '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( M + 1 ) ( + , %s ) e. dom ~~> ) )' % (A0, GN, GN))],
           'mpbid', '( %s -> seq ( M + 1 ) ( + , %s ) e. dom ~~> )' % (A0, GN))
cvgau = w.s([cvga, w.s([nu1, m1n, abcc], 'iserex',
                       '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( M + 1 ) ( + , %s ) e. dom ~~> ) )' % (A0, ABN, ABN))],
            'mpbid', '( %s -> seq ( M + 1 ) ( + , %s ) e. dom ~~> )' % (A0, ABN))
mju = w.s([mjA, w.s([nu1, m1n, hcc], 'iserex',
                    '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( M + 1 ) ( + , %s ) e. dom ~~> ) )' % (A0, HNZ, HNZ))],
          'mpbid', '( %s -> seq ( M + 1 ) ( + , %s ) e. dom ~~> )' % (A0, HNZ))
equ = w.s([], 'eqid', '%s = %s' % (UZ, UZ))
lg = w.s([equ, m1z, vGU, trmU, cvgu], 'isumclim2',
         '( %s -> seq ( M + 1 ) ( + , %s ) ~~> sum_ k e. %s %s )' % (A0, GN, UZ, TRMK))
abreU = w.s([trmU], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Au, TRMK))
la = w.s([equ, m1z, vABU, w.s([abreU], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Au, TRMK)), cvgau], 'isumclim2',
         '( %s -> seq ( M + 1 ) ( + , %s ) ~~> sum_ k e. %s ( abs ` %s ) )' % (A0, ABN, UZ, TRMK))
abvU = w.s([vABU, w.s([vGU], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Au, GN, TRMK))],
           'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Au, ABN, GN))
gccU = w.s([vGU, trmU], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Au, GN))
step1 = w.s([equ, lg, la, m1z, gccU, abvU], 'iserabs',
            '( %s -> ( abs ` sum_ k e. %s %s ) <_ sum_ k e. %s ( abs ` %s ) )' % (A0, UZ, TRMK, UZ, TRMK))
prreU = w.s([prpU], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Au, RZ))
hreU = w.s([crU, prreU], 'remulcld', '( %s -> ( C x. ( k ^c -u %s ) ) e. RR )' % (Au, RZ))
step2 = w.s([equ, m1z, vABU, abreU, vHU, hreU, bndU, cvgau, mju], 'isumle',
            '( %s -> sum_ k e. %s ( abs ` %s ) <_ sum_ k e. %s ( C x. ( k ^c -u %s ) ) )' % (A0, UZ, TRMK, UZ, RZ))
zcvu = w.s([w.s([w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)),
                      w.inst('zsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, FNZ)),
                w.s([nu1, m1n, w.s([t['vF'], w.s([w.s([t['prp']], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))],
                                                 'recnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Ak, RZ))], 'eqeltrd',
                                    '( %s -> ( %s ` k ) e. CC )' % (Ak, FNZ))], 'iserex',
                    '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( M + 1 ) ( + , %s ) e. dom ~~> ) )' % (A0, FNZ, FNZ))],
               'mpbid', '( %s -> seq ( M + 1 ) ( + , %s ) e. dom ~~> )' % (A0, FNZ))], 'idi',
           '( %s -> seq ( M + 1 ) ( + , %s ) e. dom ~~> )' % (A0, FNZ))
mc = w.s([equ, m1z, w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0), vFU,
          w.s([prpU], 'rpcnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Au, RZ)), zcvu], 'isummulc2',
         '( %s -> ( C x. sum_ k e. %s ( k ^c -u %s ) ) = sum_ k e. %s ( C x. ( k ^c -u %s ) ) )' % (A0, UZ, RZ, UZ, RZ))
zt = w.s([w.s([w.s([d['rz'], d['zgt']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)), mn], 'jca',
              '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ M e. NN ) )' % (A0, RZ, RZ)), w.inst('zsertail')], 'syl',
         '( %s -> sum_ k e. %s ( k ^c -u %s ) <_ ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) )' % (A0, UZ, RZ, RZ, RZ))
# closures for the final chain
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
tm1rp = w.s([w.s([d['rz'], r1], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (A0, RZ)),
             w.s([d['zgt'], w.s([r1, d['rz']], 'posdifd', '( %s -> ( 1 < %s <-> 0 < ( %s - 1 ) ) )' % (A0, RZ, RZ))],
                 'mpbid', '( %s -> 0 < ( %s - 1 ) )' % (A0, RZ))], 'elrpd', '( %s -> ( %s - 1 ) e. RR+ )' % (A0, RZ))
pmrp = w.s([w.s([mn], 'nnrpd', '( %s -> M e. RR+ )' % A0), w.s([r1, d['rz']], 'resubcld', '( %s -> ( 1 - %s ) e. RR )' % (A0, RZ))],
           'rpcxpcld', '( %s -> ( M ^c ( 1 - %s ) ) e. RR+ )' % (A0, RZ))
bndre = w.s([w.s([pmrp, tm1rp], 'rpdivcld', '( %s -> ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) e. RR+ )' % (A0, RZ, RZ))],
            'rpred', '( %s -> ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) e. RR )' % (A0, RZ, RZ))
zsre = w.s([equ, m1z, vFU, prreU, zcvu], 'isumrecl', '( %s -> sum_ k e. %s ( k ^c -u %s ) e. RR )' % (A0, UZ, RZ))
mul = w.s([w.s([zsre, bndre, w.s([d['cr'], d['c0']], 'jca', '( %s -> ( C e. RR /\\ 0 <_ C ) )' % A0)], '3jca',
                '( %s -> ( sum_ k e. %s ( k ^c -u %s ) e. RR /\\ ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) e. RR /\\ ( C e. RR /\\ 0 <_ C ) ) )' % (A0, UZ, RZ, RZ, RZ)),
           zt, w.inst('lemul2a')], 'syl2anc',
          '( %s -> ( C x. sum_ k e. %s ( k ^c -u %s ) ) <_ ( C x. ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) ) )' % (A0, UZ, RZ, RZ, RZ))
mul2 = w.s([w.s([mc], 'eqcomd', '( %s -> sum_ k e. %s ( C x. ( k ^c -u %s ) ) = ( C x. sum_ k e. %s ( k ^c -u %s ) ) )' % (A0, UZ, RZ, UZ, RZ)), mul],
           'eqbrtrd', '( %s -> sum_ k e. %s ( C x. ( k ^c -u %s ) ) <_ ( C x. ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) ) )' % (A0, UZ, RZ, RZ, RZ))
sumcl = w.s([equ, m1z, vGU, trmU, cvgu], 'isumcl', '( %s -> sum_ k e. %s %s e. CC )' % (A0, UZ, TRMK))
absre = w.s([sumcl], 'abscld', '( %s -> ( abs ` sum_ k e. %s %s ) e. RR )' % (A0, UZ, TRMK))
absum = w.s([equ, m1z, vABU, abreU, cvgau], 'isumrecl', '( %s -> sum_ k e. %s ( abs ` %s ) e. RR )' % (A0, UZ, TRMK))
msum = w.s([equ, m1z, vHU, hreU, mju], 'isumrecl', '( %s -> sum_ k e. %s ( C x. ( k ^c -u %s ) ) e. RR )' % (A0, UZ, RZ))
cbre = w.s([d['cr'], bndre], 'remulcld', '( %s -> ( C x. ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) ) e. RR )' % (A0, RZ, RZ))
st1 = w.s([absre, absum, msum, step1, step2], 'letrd',
          '( %s -> ( abs ` sum_ k e. %s %s ) <_ sum_ k e. %s ( C x. ( k ^c -u %s ) ) )' % (A0, UZ, TRMK, UZ, RZ))
w.qed([absre, msum, cbre, st1, mul2], 'letrd',
      '( %s -> ( abs ` sum_ k e. %s %s ) <_ ( C x. ( ( M ^c ( 1 - %s ) ) / ( %s - 1 ) ) ) )' % (A0, UZ, TRMK, RZ, RZ)); run3(w)
