"""Sortie C3 section 3: the termwise estimates."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

HT = HP('T'); HU = HP('U')

# ---- hpssd -----------------------------------------------------------------
w = W('hpssd', 'The half-planes are nested: a larger abscissa gives a smaller half-plane.')
A0 = '( T e. RR /\\ U e. RR /\\ T <_ U )'
A1 = '( %s /\\ z e. %s )' % (A0, HU)
tr = w.s([], 'simp1', '( %s -> T e. RR )' % A0)
ur = w.s([], 'simp2', '( %s -> U e. RR )' % A0)
le = w.s([], 'simp3', '( %s -> T <_ U )' % A0)
elu = w.s([ur, w.inst('elhp2')], 'syl', '( %s -> ( z e. %s <-> ( z e. CC /\\ U < ( Re ` z ) ) ) )' % (A0, HU))
elt = w.s([tr, w.inst('elhp2')], 'syl', '( %s -> ( z e. %s <-> ( z e. CC /\\ T < ( Re ` z ) ) ) )' % (A0, HT))
mem = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, HU))
p = w.s([mem, w.s([elu], 'adantr', '( %s -> ( z e. %s <-> ( z e. CC /\\ U < ( Re ` z ) ) ) )' % (A1, HU))],
        'mpbid', '( %s -> ( z e. CC /\\ U < ( Re ` z ) ) )' % A1)
zc = w.s([p, w.inst('simpl')], 'syl', '( %s -> z e. CC )' % A1)
lt = w.s([p, w.inst('simpr')], 'syl', '( %s -> U < ( Re ` z ) )' % A1)
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> ( Re ` z ) e. RR )' % A1)
lt2 = w.s([w.s([tr], 'adantr', '( %s -> T e. RR )' % A1), w.s([ur], 'adantr', '( %s -> U e. RR )' % A1), rz,
           w.s([le], 'adantr', '( %s -> T <_ U )' % A1), lt], 'lelttrd', '( %s -> T < ( Re ` z ) )' % A1)
q = w.s([zc, lt2], 'jca', '( %s -> ( z e. CC /\\ T < ( Re ` z ) ) )' % A1)
inn = w.s([q, w.s([elt], 'adantr', '( %s -> ( z e. %s <-> ( z e. CC /\\ T < ( Re ` z ) ) ) )' % (A1, HT))],
          'mpbird', '( %s -> z e. %s )' % (A1, HT))
w.qed([w.s([inn], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (A0, HU, HT))], 'ssrdv',
      '( %s -> %s C_ %s )' % (A0, HU, HT)); run3(w)

# ---- cxpnnabs --------------------------------------------------------------
w = W('cxpnnabs', 'The modulus of a Dirichlet-series power: it depends only on the real part of the exponent.')
A0 = '( K e. NN /\\ Z e. CC )'
kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
zc = w.s([], 'simpr', '( %s -> Z e. CC )' % A0)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
nz = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0)
ab = w.s([krp, nz, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` ( K ^c -u Z ) ) = ( K ^c ( Re ` -u Z ) ) )' % A0)
rn = w.s([zc, w.inst('reneg')], 'syl', '( %s -> ( Re ` -u Z ) = -u ( Re ` Z ) )' % A0)
w.qed([ab, w.s([rn], 'oveq2d', '( %s -> ( K ^c ( Re ` -u Z ) ) = ( K ^c -u ( Re ` Z ) ) )' % A0)],
      'eqtrd', '( %s -> ( abs ` ( K ^c -u Z ) ) = ( K ^c -u ( Re ` Z ) ) )' % A0); run3(w)

# ---- cxpnnle ---------------------------------------------------------------
w = W('cxpnnle', 'The Dirichlet-series majorant: a smaller abscissa gives a larger term.')
A0 = '( ( K e. NN /\\ T e. RR /\\ Z e. CC ) /\\ T <_ ( Re ` Z ) )'
kn = w.s([], 'simpl1', '( %s -> K e. NN )' % A0)
tr = w.s([], 'simpl2', '( %s -> T e. RR )' % A0)
zc = w.s([], 'simpl3', '( %s -> Z e. CC )' % A0)
le = w.s([], 'simpr', '( %s -> T <_ ( Re ` Z ) )' % A0)
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> ( Re ` Z ) e. RR )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0)
k1 = w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)
nr = w.s([rz], 'renegcld', '( %s -> -u ( Re ` Z ) e. RR )' % A0)
nt = w.s([tr], 'renegcld', '( %s -> -u T e. RR )' % A0)
nle = w.s([le, w.s([tr, rz], 'lenegd', '( %s -> ( T <_ ( Re ` Z ) <-> -u ( Re ` Z ) <_ -u T ) )' % A0)],
          'mpbid', '( %s -> -u ( Re ` Z ) <_ -u T )' % A0)
l = w.s([kr, k1], 'jca', '( %s -> ( K e. RR /\\ 1 <_ K ) )' % A0)
m = w.s([nr, nt], 'jca', '( %s -> ( -u ( Re ` Z ) e. RR /\\ -u T e. RR ) )' % A0)
w.qed([l, m, nle, w.inst('cxplea')], 'syl3anc',
      '( %s -> ( K ^c -u ( Re ` Z ) ) <_ ( K ^c -u T ) )' % A0); run3(w)
