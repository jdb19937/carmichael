"""C7, Gamma block 2: the two exponential tails, the continuity and
integrability of 2 ^c -u ( |u| / 4 ), the full-line bound and the weighted
Gamma line moment (exp4itg, exp4itgn, exp4cn, exp4ibl, exp4itg2, gamlmom)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq, nlinarith

L2 = '( log ` 2 )'
A0 = 'T e. RR+'
FOURL = '( 4 / %s )' % L2


def EK2(K, u):
    return '( 2 ^c ( %s x. %s ) )' % (K, u)


def tail(w, K, A, B, TGT, VNAME):
    """under A0, S. ( A (,) B ) TGT _d u <_ ( 4 / log 2 ) where TGT = 2 ^c (K x. u)
    rewritten; VNAME is the endpoint value at the non-zero end"""
    X = '( %s (,) %s )' % (A, B)
    trp = w.s([], 'id', '( %s -> T e. RR+ )' % A0)
    cl = Closure(w, A0, {'T': ('RR+', trp)})
    tr = cl.mem('T', 'RR')
    l2r = w.s([a1(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L2))
    cl.leaf(L2, 'RR', l2r)
    l2ge = a1(w, A0, 'log2ge', '( 1 / 2 ) <_ %s' % L2)
    l2gt = linarith(w, A0, [l2ge], '0 < %s' % L2, closure=cl)
    l2rp = w.s([l2r, l2gt], 'elrpd', '( %s -> %s e. RR+ )' % (A0, L2))
    cl.have(L2, 'RR+', l2rp)
    kr = cl.mem(K, 'RR'); kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A0, K))
    if K.startswith('-u '):
        K1 = K[3:]
        kne = w.s([w.s([cl.mem(K1, 'RR')], 'recnd', '( %s -> %s e. CC )' % (A0, K1)), cl.ne0(K1)], 'negne0d', '( %s -> %s =/= 0 )' % (A0, K))
    else:
        kne = cl.ne0(K)
    ar = cl.mem(A, 'RR'); br = cl.mem(B, 'RR')
    le = linarith(w, A0, [cl.gt0('T')], '%s <_ %s' % (A, B), closure=cl)
    h2 = w.s([a1(w, A0, '2rp', '2 e. RR+'), w.s([w.s([w.s([], '1ne2', '1 =/= 2')], 'necomi', '2 =/= 1')], 'a1i', '( %s -> 2 =/= 1 )' % A0)], 'jca', '( %s -> ( 2 e. RR+ /\\ 2 =/= 1 ) )' % A0)
    hk = w.s([w.s([kr, kne], 'jca', '( %s -> ( %s e. RR /\\ %s =/= 0 ) )' % (A0, K, K)), w.s([ar, br, le], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) )' % (A0, A, B, A, B))], 'jca',
             '( %s -> ( ( %s e. RR /\\ %s =/= 0 ) /\\ ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) ) )' % (A0, K, K, A, B, A, B))
    KL = '( %s x. %s )' % (K, L2)
    itg = w.s([w.s([h2, hk], 'jca', '( %s -> ( ( 2 e. RR+ /\\ 2 =/= 1 ) /\\ ( ( %s e. RR /\\ %s =/= 0 ) /\\ ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) ) ) )' % (A0, K, K, A, B, A, B)), w.inst('cxpaffitg2')], 'syl',
              '( %s -> S. %s %s _d u = ( ( %s - %s ) / %s ) )' % (A0, X, EK2(K, 'u'), EK2(K, B), EK2(K, A), KL))
    # the integrand
    AT = '( %s /\\ u e. %s )' % (A0, X)
    ur = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (AT, X)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % AT)
    clt = Closure(w, AT, {'u': ('RR', ur)})
    rw = lineq(w, AT, TGT[1], '( %s x. u )' % K, closure=clt)
    rwi = w.s([w.s([rw], 'oveq2d', '( %s -> %s = %s )' % (AT, TGT[0], EK2(K, 'u')))], 'itgeq2dv', '( %s -> S. %s %s _d u = S. %s %s _d u )' % (A0, X, TGT[0], X, EK2(K, 'u')))
    # the value at 0
    z = w.s([w.s([w.s([kc], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (A0, K))], 'oveq2d', '( %s -> %s = ( 2 ^c 0 ) )' % (A0, EK2(K, '0'))),
             w.s([w.s([w.s([], '2cn', '2 e. CC'), w.inst('cxp0')], 'ax-mp', '( 2 ^c 0 ) = 1')], 'a1i', '( %s -> ( 2 ^c 0 ) = 1 )' % A0)], 'eqtrd', '( %s -> %s = 1 )' % (A0, EK2(K, '0')))
    other = B if A == '0' else A
    V = EK2(K, other)
    vrp = w.s([a1(w, A0, '2rp', '2 e. RR+'), cl.mem('( %s x. %s )' % (K, other), 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, V))
    cl.leaf(V, 'RR+', vrp)
    vr = cl.mem(V, 'RR'); v0 = w.s([vrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, V))
    NUM0 = '( %s - %s )' % (EK2(K, B), EK2(K, A))
    NUM = '( %s - 1 )' % V if A == '0' else '( 1 - %s )' % V
    numeq = w.s([z], 'oveq2d' if A == '0' else 'oveq1d', '( %s -> %s = %s )' % (A0, NUM0, NUM))
    numr = cl.mem(NUM, 'RR'); numc = w.s([numr], 'recnd', '( %s -> %s e. CC )' % (A0, NUM))
    l2c = w.s([l2r], 'recnd', '( %s -> %s e. CC )' % (A0, L2)); l2ne = w.s([l2rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, L2))
    VAL = '( %s / %s )' % (NUM, KL)
    klc = w.s([kc, l2c], 'mulcld', '( %s -> %s e. CC )' % (A0, KL)); klne = w.s([kc, l2c, kne, l2ne], 'mulne0d', '( %s -> %s =/= 0 )' % (A0, KL))
    cl.have(KL, 'ne0', klne)
    valr = cl.mem(VAL, 'RR'); cl.atom(VAL)
    hh = w.s([numc, klc, klne], 'divcan1d', '( %s -> ( %s x. %s ) = %s )' % (A0, VAL, KL, NUM))
    b4 = linarith(w, A0, [hh, v0], '( %s x. %s ) <_ 4' % (VAL, L2), closure=cl, products=True)
    lmd = w.s([valr, a1(w, A0, '4re', '4 e. RR'), w.s([l2r, l2gt], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, L2, L2)), w.inst('lemuldiv')], 'syl3anc',
              '( %s -> ( ( %s x. %s ) <_ 4 <-> %s <_ %s ) )' % (A0, VAL, L2, VAL, FOURL))
    vle = w.s([b4, lmd], 'mpbid', '( %s -> %s <_ %s )' % (A0, VAL, FOURL))
    tot = w.s([w.s([rwi, itg], 'eqtrd', '( %s -> S. %s %s _d u = ( %s / %s ) )' % (A0, X, TGT[0], NUM0, KL)),
               w.s([numeq], 'oveq1d', '( %s -> ( %s / %s ) = %s )' % (A0, NUM0, KL, VAL))], 'eqtrd', '( %s -> S. %s %s _d u = %s )' % (A0, X, TGT[0], VAL))
    w.qed([tot, vle], 'eqbrtrd', '( %s -> S. %s %s _d u <_ %s )' % (A0, X, TGT[0], FOURL))


# ---------------------------------------------------------------- exp4itg
w = W('exp4itg', 'The right tail of the line-moment majorant: ` S. ( 0 (,) T ) 2 ^c -u ( u / 4 ) '
      '_d u <_ 4 / log 2 ` ( ~ cxpaffitg2 at base ` 2 ` and slope ` -u ( 1 / 4 ) `).')
tail(w, '-u ( 1 / 4 )', '0', 'T', ('( 2 ^c -u ( u / 4 ) )', '-u ( u / 4 )'), None)
run7(w)

# ---------------------------------------------------------------- exp4itgn
w = W('exp4itgn', 'The left tail of the line-moment majorant: ` S. ( -u T (,) 0 ) 2 ^c ( u / 4 ) '
      '_d u <_ 4 / log 2 ` ( ~ cxpaffitg2 at base ` 2 ` and slope ` 1 / 4 `).')
tail(w, '( 1 / 4 )', '-u T', '0', ('( 2 ^c ( u / 4 ) )', '( u / 4 )'), None)
run7(w)

# ---------------------------------------------------------------- exp4cn
R = '( 2 ^c -u ( ( abs ` u ) / 4 ) )'
XC = '( -u T [,] T )'
XO = '( -u T (,) T )'
XL = '( -u T (,) 0 )'
XR = '( 0 (,) T )'
KC = '( -u ( 1 / 4 ) x. %s )' % L2
w = W('exp4cn', 'The line-moment majorant ` 2 ^c -u ( |u| / 4 ) ` is continuous on the '
      'closed interval ` [ -u T , T ] ` (through ` exp ` and ~ abscncf ).')
trp = w.s([], 'id', '( %s -> T e. RR+ )' % A0)
cl = Closure(w, A0, {'T': ('RR+', trp)})
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
l2r = w.s([a1(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L2))
cl.leaf(L2, 'RR', l2r)
kcr = cl.mem(KC, 'RR'); kcc = w.s([kcr], 'recnd', '( %s -> %s e. CC )' % (A0, KC))
ussr = w.s([ntr, tr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, XC))
usscn = w.s([ussr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XC))
sscc = a1(w, A0, 'ssid', 'CC C_ CC')
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( u e. %s |-> u ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
abss = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
absf = w.s([w.s([abss, w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'sselii', 'abs e. ( CC -cn-> CC )')], 'a1i', '( %s -> abs e. ( CC -cn-> CC ) )' % A0)
absm = w.s([absf, idc], 'cncfmpt1f', '( %s -> ( u e. %s |-> ( abs ` u ) ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
kcst = w.s([kcc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, KC, XC))
mul = w.s([absm, kcst], 'mulcncf', '( %s -> ( u e. %s |-> ( ( abs ` u ) x. %s ) ) e. ( %s -cn-> CC ) )' % (A0, XC, KC, XC))
efc = a1(w, A0, 'efcn', 'exp e. ( CC -cn-> CC )')
cmp = w.s([efc, mul], 'cncfmpt1f', '( %s -> ( u e. %s |-> ( exp ` ( ( abs ` u ) x. %s ) ) ) e. ( %s -cn-> CC ) )' % (A0, XC, KC, XC))
ATC = '( %s /\\ u e. %s )' % (A0, XC)
ur = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> u e. %s )' % (ATC, XC))], 'sseldd', '( %s -> u e. RR )' % ATC)
aur = w.s([w.s([ur], 'recnd', '( %s -> u e. CC )' % ATC)], 'abscld', '( %s -> ( abs ` u ) e. RR )' % ATC)
clt = Closure(w, ATC, {})
clt.leaf('( abs ` u )', 'RR', aur); clt.leaf(L2, 'RR', w.s([l2r], 'adantr', '( %s -> %s e. RR )' % (ATC, L2)))
EXP = '-u ( ( abs ` u ) / 4 )'
expc = w.s([clt.mem(EXP, 'RR')], 'recnd', '( %s -> %s e. CC )' % (ATC, EXP))
cef = w.s([a1(w, ATC, '2cn', '2 e. CC'), a1(w, ATC, '2ne0', '2 =/= 0'), expc, w.inst('cxpef')], 'syl3anc', '( %s -> %s = ( exp ` ( %s x. %s ) ) )' % (ATC, R, EXP, L2))
rw = lineq(w, ATC, '( %s x. %s )' % (EXP, L2), '( ( abs ` u ) x. %s )' % KC, closure=clt, products=True)
pt = w.s([cef, w.s([rw], 'fveq2d', '( %s -> ( exp ` ( %s x. %s ) ) = ( exp ` ( ( abs ` u ) x. %s ) ) )' % (ATC, EXP, L2, KC))], 'eqtrd', '( %s -> %s = ( exp ` ( ( abs ` u ) x. %s ) ) )' % (ATC, R, KC))
w.qed([w.s([pt], 'mpteq2dva', '( %s -> ( u e. %s |-> %s ) = ( u e. %s |-> ( exp ` ( ( abs ` u ) x. %s ) ) ) )' % (A0, XC, R, XC, KC)), cmp], 'eqeltrd',
      '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, R, XC))
run7(w)

# ---------------------------------------------------------------- exp4ibl
w = W('exp4ibl', 'The line-moment majorant ` 2 ^c -u ( |u| / 4 ) ` is integrable on '
      '` ( -u T , T ) ` and on its two halves ( ~ exp4cn , ~ cniccibl , ~ iblss ).')
trp = w.s([], 'id', '( %s -> T e. RR+ )' % A0)
cl = Closure(w, A0, {'T': ('RR+', trp)})
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
full = w.s([ntr, tr, w.s([trp, w.inst('exp4cn')], 'syl', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, R, XC)), w.inst('cniccibl')], 'syl3anc',
           '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XC, R))
ATC = '( %s /\\ u e. %s )' % (A0, XC)
ussr = w.s([ntr, tr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, XC))
ur = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> u e. %s )' % (ATC, XC))], 'sseldd', '( %s -> u e. RR )' % ATC)
aur = w.s([w.s([ur], 'recnd', '( %s -> u e. CC )' % ATC)], 'abscld', '( %s -> ( abs ` u ) e. RR )' % ATC)
clt = Closure(w, ATC, {})
clt.leaf('( abs ` u )', 'RR', aur)
rc = w.s([w.s([a1(w, ATC, '2rp', '2 e. RR+'), clt.mem('-u ( ( abs ` u ) / 4 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (ATC, R))], 'rpcnd', '( %s -> %s e. CC )' % (ATC, R))
ntxr = w.s([ntr], 'rexrd', '( %s -> -u T e. RR* )' % A0); txr = w.s([tr], 'rexrd', '( %s -> T e. RR* )' % A0)
xrp = w.s([ntxr, txr], 'jca', '( %s -> ( -u T e. RR* /\\ T e. RR* ) )' % A0)
nt0 = linarith(w, A0, [cl.gt0('T')], '-u T <_ 0', closure=cl); t0 = linarith(w, A0, [cl.gt0('T')], '0 <_ T', closure=cl)
ntle = w.s([ntr], 'leidd', '( %s -> -u T <_ -u T )' % A0); tle = w.s([tr], 'leidd', '( %s -> T <_ T )' % A0)
ioc = a1(w, A0, 'ioossicc', '%s C_ %s' % (XO, XC))


def part(XX, l1, f1, l2, f2):
    ss = w.s([w.s([xrp, w.s([l1, l2], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, f1, f2))], 'jca',
                  '( %s -> ( ( -u T e. RR* /\\ T e. RR* ) /\\ ( %s /\\ %s ) ) )' % (A0, f1, f2)), w.inst('ioossioo')], 'syl',
             '( %s -> %s C_ %s )' % (A0, XX, XO))
    ss2 = w.s([ss, ioc], 'sstrd', '( %s -> %s C_ %s )' % (A0, XX, XC))
    return w.s([ss2, a1(w, A0, 'ioombl', '%s e. dom vol' % XX), rc, full], 'iblss', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XX, R))


i0 = w.s([ioc, a1(w, A0, 'ioombl', '%s e. dom vol' % XO), rc, full], 'iblss', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XO, R))
il = part(XL, ntle, '-u T <_ -u T', t0, '0 <_ T')
ir = part(XR, nt0, '-u T <_ 0', tle, 'T <_ T')
w.qed([i0, w.s([il, ir], 'jca', '( %s -> ( ( u e. %s |-> %s ) e. L^1 /\\ ( u e. %s |-> %s ) e. L^1 ) )' % (A0, XL, R, XR, R))], 'jca',
      '( %s -> ( ( u e. %s |-> %s ) e. L^1 /\\ ( ( u e. %s |-> %s ) e. L^1 /\\ ( u e. %s |-> %s ) e. L^1 ) ) )' % (A0, XO, R, XL, R, XR, R))
run7(w)

# ---------------------------------------------------------------- exp4itg2
EIGHTL = '( 8 / %s )' % L2
w = W('exp4itg2', 'The line-moment majorant integrates to at most ` 8 / log 2 ` over '
      '` ( -u T , T ) `: the split at ` 0 ` ( ~ itgsplitioo ) and the two tails '
      '~ exp4itgn , ~ exp4itg .')
trp = w.s([], 'id', '( %s -> T e. RR+ )' % A0)
cl = Closure(w, A0, {'T': ('RR+', trp)})
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
l2r = w.s([a1(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L2))
cl.leaf(L2, 'RR', l2r)
l2ge = a1(w, A0, 'log2ge', '( 1 / 2 ) <_ %s' % L2)
l2gt = linarith(w, A0, [l2ge], '0 < %s' % L2, closure=cl)
l2rp = w.s([l2r, l2gt], 'elrpd', '( %s -> %s e. RR+ )' % (A0, L2))
ibl = w.s([trp, w.inst('exp4ibl')], 'syl', '( %s -> ( ( u e. %s |-> %s ) e. L^1 /\\ ( ( u e. %s |-> %s ) e. L^1 /\\ ( u e. %s |-> %s ) e. L^1 ) ) )' % (A0, XO, R, XL, R, XR, R))
ibl2 = w.s([ibl, w.inst('simpr')], 'syl', '( %s -> ( ( u e. %s |-> %s ) e. L^1 /\\ ( u e. %s |-> %s ) e. L^1 ) )' % (A0, XL, R, XR, R))
ill = w.s([ibl2, w.inst('simpl')], 'syl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XL, R))
irr = w.s([ibl2, w.inst('simpr')], 'syl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XR, R))
nt0 = linarith(w, A0, [cl.gt0('T')], '-u T <_ 0', closure=cl); t0 = linarith(w, A0, [cl.gt0('T')], '0 <_ T', closure=cl)
zin = w.s([w.s([a1(w, A0, '0re', '0 e. RR'), nt0, t0], '3jca', '( %s -> ( 0 e. RR /\\ -u T <_ 0 /\\ 0 <_ T ) )' % A0), w.s([ntr, tr, w.inst('elicc2')], 'syl2anc', '( %s -> ( 0 e. %s <-> ( 0 e. RR /\\ -u T <_ 0 /\\ 0 <_ T ) ) )' % (A0, XC))],
          'mpbird', '( %s -> 0 e. %s )' % (A0, XC))
ATO = '( %s /\\ u e. %s )' % (A0, XO)
ur = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (ATO, XO)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % ATO)
aur = w.s([w.s([ur], 'recnd', '( %s -> u e. CC )' % ATO)], 'abscld', '( %s -> ( abs ` u ) e. RR )' % ATO)
clt = Closure(w, ATO, {}); clt.leaf('( abs ` u )', 'RR', aur)
rc = w.s([w.s([a1(w, ATO, '2rp', '2 e. RR+'), clt.mem('-u ( ( abs ` u ) / 4 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (ATO, R))], 'rpcnd', '( %s -> %s e. CC )' % (ATO, R))
spl = w.s([ntr, tr, zin, rc, ill, irr], 'itgsplitioo', '( %s -> S. %s %s _d u = ( S. %s %s _d u + S. %s %s _d u ) )' % (A0, XO, R, XL, R, XR, R))
# the left half
ATL = '( %s /\\ u e. %s )' % (A0, XL)
url = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (ATL, XL)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % ATL)
ult = w.s([w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (ATL, XL)), w.inst('eliooord')], 'syl', '( %s -> ( -u T < u /\\ u < 0 ) )' % ATL), w.inst('simpr')], 'syl', '( %s -> u < 0 )' % ATL)
cll = Closure(w, ATL, {'u': ('RR', url)})
cll.leaf('( abs ` u )', 'RR', w.s([w.s([url], 'recnd', '( %s -> u e. CC )' % ATL)], 'abscld', '( %s -> ( abs ` u ) e. RR )' % ATL))
ule = linarith(w, ATL, [ult], 'u <_ 0', closure=cll)
absl = w.s([url, ule], 'absnidd', '( %s -> ( abs ` u ) = -u u )' % ATL)
lft = w.s([w.s([w.s([w.s([absl], 'oveq1d', '( %s -> ( ( abs ` u ) / 4 ) = ( -u u / 4 ) )' % ATL)], 'negeqd', '( %s -> -u ( ( abs ` u ) / 4 ) = -u ( -u u / 4 ) )' % ATL),
                lineq(w, ATL, '-u ( -u u / 4 )', '( u / 4 )', closure=cll)], 'eqtrd', '( %s -> -u ( ( abs ` u ) / 4 ) = ( u / 4 ) )' % ATL)], 'oveq2d', '( %s -> %s = ( 2 ^c ( u / 4 ) ) )' % (ATL, R))
lfti = w.s([lft], 'itgeq2dv', '( %s -> S. %s %s _d u = S. %s ( 2 ^c ( u / 4 ) ) _d u )' % (A0, XL, R, XL))
lb = w.s([lfti, w.s([trp, w.inst('exp4itgn')], 'syl', '( %s -> S. %s ( 2 ^c ( u / 4 ) ) _d u <_ %s )' % (A0, XL, FOURL))], 'eqbrtrd', '( %s -> S. %s %s _d u <_ %s )' % (A0, XL, R, FOURL))
# the right half
ATR = '( %s /\\ u e. %s )' % (A0, XR)
urr = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (ATR, XR)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % ATR)
ugt = w.s([w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (ATR, XR)), w.inst('eliooord')], 'syl', '( %s -> ( 0 < u /\\ u < T ) )' % ATR), w.inst('simpl')], 'syl', '( %s -> 0 < u )' % ATR)
clr = Closure(w, ATR, {'u': ('RR', urr)})
clr.leaf('( abs ` u )', 'RR', w.s([w.s([urr], 'recnd', '( %s -> u e. CC )' % ATR)], 'abscld', '( %s -> ( abs ` u ) e. RR )' % ATR))
uge = linarith(w, ATR, [ugt], '0 <_ u', closure=clr)
absr = w.s([urr, uge], 'absidd', '( %s -> ( abs ` u ) = u )' % ATR)
rgt = w.s([w.s([w.s([absr], 'oveq1d', '( %s -> ( ( abs ` u ) / 4 ) = ( u / 4 ) )' % ATR)], 'negeqd', '( %s -> -u ( ( abs ` u ) / 4 ) = -u ( u / 4 ) )' % ATR)], 'oveq2d', '( %s -> %s = ( 2 ^c -u ( u / 4 ) ) )' % (ATR, R))
rgti = w.s([rgt], 'itgeq2dv', '( %s -> S. %s %s _d u = S. %s ( 2 ^c -u ( u / 4 ) ) _d u )' % (A0, XR, R, XR))
rb = w.s([rgti, w.s([trp, w.inst('exp4itg')], 'syl', '( %s -> S. %s ( 2 ^c -u ( u / 4 ) ) _d u <_ %s )' % (A0, XR, FOURL))], 'eqbrtrd', '( %s -> S. %s %s _d u <_ %s )' % (A0, XR, R, FOURL))
# the sum
rrl = w.s([w.s([a1(w, ATL, '2rp', '2 e. RR+'), cll.mem('-u ( ( abs ` u ) / 4 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (ATL, R))], 'rpred', '( %s -> %s e. RR )' % (ATL, R))
rrr = w.s([w.s([a1(w, ATR, '2rp', '2 e. RR+'), clr.mem('-u ( ( abs ` u ) / 4 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (ATR, R))], 'rpred', '( %s -> %s e. RR )' % (ATR, R))
il_r = w.s([rrl, ill], 'itgrecl', '( %s -> S. %s %s _d u e. RR )' % (A0, XL, R))
ir_r = w.s([rrr, irr], 'itgrecl', '( %s -> S. %s %s _d u e. RR )' % (A0, XR, R))
fourr = w.s([a1(w, A0, '4re', '4 e. RR'), l2rp], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, FOURL))
sum_ = w.s([il_r, ir_r, fourr, fourr, lb, rb], 'le2addd', '( %s -> ( S. %s %s _d u + S. %s %s _d u ) <_ ( %s + %s ) )' % (A0, XL, R, XR, R, FOURL, FOURL))
c4 = a1(w, A0, '4cn', '4 e. CC')
eight = w.s([w.s([w.s([c4, c4, w.s([l2r], 'recnd', '( %s -> %s e. CC )' % (A0, L2)), w.s([l2rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, L2))], 'divdird', '( %s -> ( ( 4 + 4 ) / %s ) = ( %s + %s ) )' % (A0, L2, FOURL, FOURL))], 'eqcomd',
                '( %s -> ( %s + %s ) = ( ( 4 + 4 ) / %s ) )' % (A0, FOURL, FOURL, L2)),
           w.s([a1(w, A0, '4p4e8', '( 4 + 4 ) = 8')], 'oveq1d', '( %s -> ( ( 4 + 4 ) / %s ) = %s )' % (A0, L2, EIGHTL))], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, FOURL, FOURL, EIGHTL))
w.qed([spl, w.s([sum_, eight], 'breqtrd', '( %s -> ( S. %s %s _d u + S. %s %s _d u ) <_ %s )' % (A0, XL, R, XR, R, EIGHTL))], 'eqbrtrd', '( %s -> S. %s %s _d u <_ %s )' % (A0, XO, R, EIGHTL))
run7(w)

# ---------------------------------------------------------------- gamlmom
w = W('gamlmom', 'The weighted Gamma line moment, truncated: ` S. ( -u T (,) T ) |Gamma ( X + i u )| '
      '( 1 + |u| ) ^ 2 _d u <_ 1024 H / log 2 ` for any strip constant ` H ` of ~ gamstrb '
      'and any ` T `, with a bound independent of ` T `.  This is ` integral_norm_Gamma_line_le ` '
      'of Route Z\'s GammaStrip.lean in truncated form (C4 blueprint 0.2 deviation 5); the '
      'integrability of the integrand is a hypothesis because set.mm has no continuity of '
      '` _G ` on a line.')
hyp(w, '1', 'gamlmom.x', '( ph -> ( X e. RR /\\ %s <_ X /\\ X <_ 3 ) )' % HUND)
hyp(w, '2', 'gamlmom.t', '( ph -> T e. RR+ )')
hyp(w, '3', 'gamlmom.h', '( ph -> ( H e. RR+ /\\ %s ) )' % GSB)
hyp(w, '4', 'gamlmom.i', '( ph -> ( u e. %s |-> %s ) e. L^1 )' % (XO, GML))
P = 'ph'
xr = w.s(['1', w.inst('simp1')], 'syl', '( ph -> X e. RR )')
xlo = w.s(['1', w.inst('simp2')], 'syl', '( ph -> %s <_ X )' % HUND)
xhi = w.s(['1', w.inst('simp3')], 'syl', '( ph -> X <_ 3 )')
hrp = w.s(['3', w.inst('simpl')], 'syl', '( ph -> H e. RR+ )')
hall = w.s(['3', w.inst('simpr')], 'syl', '( ph -> %s )' % GSB)
cl = Closure(w, P, {'X': ('RR', xr), 'H': ('RR+', hrp), 'T': ('RR+', '2')})
xgt = linarith(w, P, [xlo], '0 < X', closure=cl)
l2r = w.s([a1(w, P, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( ph -> %s e. RR )' % L2)
cl.leaf(L2, 'RR', l2r)
l2ge = a1(w, P, 'log2ge', '( 1 / 2 ) <_ %s' % L2)
l2gt = linarith(w, P, [l2ge], '0 < %s' % L2, closure=cl)
l2rp = w.s([l2r, l2gt], 'elrpd', '( ph -> %s e. RR+ )' % L2)
# the pointwise bound
AU = '( ph /\\ u e. %s )' % XO
ur = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (AU, XO)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % AU)
xru = w.s([xr], 'adantr', '( %s -> X e. RR )' % AU)
D0 = CPT('X', 'u')
d0c = cptcl(w, AU, 'X', 'u', xru, ur)
red = w.s([xru, ur, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = X )' % (AU, D0))
imd = w.s([xru, ur, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = u )' % (AU, D0))
# the substitution instance of the strip bound
ANT = '( %s <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 )' % HUND
ANT0 = '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (HUND, D0, D0)
BND = '( abs ` ( _G ` d ) ) <_ ( H x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) )'
BND0 = '( abs ` ( _G ` %s ) ) <_ ( H x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 2 ) ) )' % (D0, D0)
e1 = w.s([], 'fveq2', '( d = %s -> ( Re ` d ) = ( Re ` %s ) )' % (D0, D0))
a1_ = w.s([e1], 'breq2d', '( d = %s -> ( %s <_ ( Re ` d ) <-> %s <_ ( Re ` %s ) ) )' % (D0, HUND, HUND, D0))
a2_ = w.s([e1], 'breq1d', '( d = %s -> ( ( Re ` d ) <_ 3 <-> ( Re ` %s ) <_ 3 ) )' % (D0, D0))
a12 = w.s([a1_, a2_], 'anbi12d', '( d = %s -> ( %s <-> %s ) )' % (D0, ANT, ANT0))
g2 = w.s([w.s([], 'fveq2', '( d = %s -> ( _G ` d ) = ( _G ` %s ) )' % (D0, D0))], 'fveq2d', '( d = %s -> ( abs ` ( _G ` d ) ) = ( abs ` ( _G ` %s ) ) )' % (D0, D0))
i2 = w.s([w.s([], 'fveq2', '( d = %s -> ( Im ` d ) = ( Im ` %s ) )' % (D0, D0))], 'fveq2d', '( d = %s -> ( abs ` ( Im ` d ) ) = ( abs ` ( Im ` %s ) ) )' % (D0, D0))
i3 = w.s([i2], 'oveq1d', '( d = %s -> ( ( abs ` ( Im ` d ) ) / 2 ) = ( ( abs ` ( Im ` %s ) ) / 2 ) )' % (D0, D0))
i4 = w.s([i3], 'negeqd', '( d = %s -> -u ( ( abs ` ( Im ` d ) ) / 2 ) = -u ( ( abs ` ( Im ` %s ) ) / 2 ) )' % (D0, D0))
i5 = w.s([i4], 'oveq2d', '( d = %s -> ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) = ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 2 ) ) )' % (D0, D0))
i6 = w.s([i5], 'oveq2d', '( d = %s -> ( H x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) = ( H x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 2 ) ) ) )' % (D0, D0))
bb = w.s([g2, i6], 'breq12d', '( d = %s -> ( %s <-> %s ) )' % (D0, BND, BND0))
sb = w.s([a12, bb], 'imbi12d', '( d = %s -> ( ( %s -> %s ) <-> ( %s -> %s ) ) )' % (D0, ANT, BND, ANT0, BND0))
inst = w.s([sb, w.s([hall], 'adantr', '( %s -> %s )' % (AU, GSB)), d0c], 'rspcdva', '( %s -> ( %s -> %s ) )' % (AU, ANT0, BND0))
lo = w.s([w.s([xlo], 'adantr', '( %s -> %s <_ X )' % (AU, HUND)), red], 'breqtrrd', '( %s -> %s <_ ( Re ` %s ) )' % (AU, HUND, D0))
hi = w.s([red, w.s([xhi], 'adantr', '( %s -> X <_ 3 )' % AU)], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ 3 )' % (AU, D0))
gb = w.s([w.s([lo, hi], 'jca', '( %s -> %s )' % (AU, ANT0)), inst], 'mpd', '( %s -> %s )' % (AU, BND0))
PP = '( 2 ^c -u ( ( abs ` u ) / 2 ) )'
imrw = w.s([w.s([w.s([w.s([w.s([imd], 'fveq2d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` u ) )' % (AU, D0))], 'oveq1d', '( %s -> ( ( abs ` ( Im ` %s ) ) / 2 ) = ( ( abs ` u ) / 2 ) )' % (AU, D0))], 'negeqd',
                       '( %s -> -u ( ( abs ` ( Im ` %s ) ) / 2 ) = -u ( ( abs ` u ) / 2 ) )' % (AU, D0))], 'oveq2d', '( %s -> ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 2 ) ) = %s )' % (AU, D0, PP))], 'oveq2d',
            '( %s -> ( H x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 2 ) ) ) = ( H x. %s ) )' % (AU, D0, PP))
GA = '( abs ` ( _G ` %s ) )' % D0
gb2 = w.s([gb, imrw], 'breqtrd', '( %s -> %s <_ ( H x. %s ) )' % (AU, GA, PP))
# closures under AU
aur = w.s([w.s([ur], 'recnd', '( %s -> u e. CC )' % AU)], 'abscld', '( %s -> ( abs ` u ) e. RR )' % AU)
au0 = w.s([w.s([ur], 'recnd', '( %s -> u e. CC )' % AU)], 'absge0d', '( %s -> 0 <_ ( abs ` u ) )' % AU)
clu = Closure(w, AU, {'H': ('RR+', w.s([hrp], 'adantr', '( %s -> H e. RR+ )' % AU))})
clu.leaf('( abs ` u )', 'RR', aur); clu.have('( abs ` u )', 'ge0', au0)
regt = w.s([w.s([xgt], 'adantr', '( %s -> 0 < X )' % AU), red], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (AU, D0))
gdm = w.s([d0c, regt, w.inst('zrenn')], 'syl2anc', '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (AU, D0))
gc = w.s([gdm, w.inst('gamcl')], 'syl', '( %s -> ( _G ` %s ) e. CC )' % (AU, D0))
gar = w.s([gc], 'abscld', '( %s -> %s e. RR )' % (AU, GA))
clu.leaf(GA, 'RR', gar)
Q = '( ( 1 + ( abs ` u ) ) ^ 2 )'
qr = clu.mem(Q, 'RR'); clu.atom(Q)
q0 = w.s([w.s([a1(w, AU, '1re', '1 e. RR'), aur], 'readdcld', '( %s -> ( 1 + ( abs ` u ) ) e. RR )' % AU)], 'sqge0d', '( %s -> 0 <_ %s )' % (AU, Q))
clu.have(Q, 'ge0', q0)
ple = w.s([w.s([aur, au0], 'jca', '( %s -> ( ( abs ` u ) e. RR /\\ 0 <_ ( abs ` u ) ) )' % AU), w.inst('pol2exp')], 'syl', '( %s -> ( %s x. %s ) <_ ( ; ; 1 2 8 x. %s ) )' % (AU, Q, PP, R))
prp = w.s([a1(w, AU, '2rp', '2 e. RR+'), clu.mem('-u ( ( abs ` u ) / 2 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (AU, PP))
rrp = w.s([a1(w, AU, '2rp', '2 e. RR+'), clu.mem('-u ( ( abs ` u ) / 4 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (AU, R))
clu.leaf(PP, 'RR+', prp); clu.leaf(R, 'RR+', rrp)
MJ = '( ( ; ; 1 2 8 x. H ) x. %s )' % R
h0 = w.s([w.s([hrp], 'adantr', '( %s -> H e. RR+ )' % AU)], 'rpge0d', '( %s -> 0 <_ H )' % AU)
ptw = nlinarith(w, AU, [gb2, ple, q0, h0], '%s <_ %s' % (GML, MJ), closure=clu)
gmlr = clu.mem(GML, 'RR'); mjr = clu.mem(MJ, 'RR')
# integrability of the majorant and the comparison
ibl = w.s(['2', w.inst('exp4ibl')], 'syl', '( ph -> ( ( u e. %s |-> %s ) e. L^1 /\\ ( ( u e. %s |-> %s ) e. L^1 /\\ ( u e. %s |-> %s ) e. L^1 ) ) )' % (XO, R, XL, R, XR, R))
ibl0 = w.s([ibl, w.inst('simpl')], 'syl', '( ph -> ( u e. %s |-> %s ) e. L^1 )' % (XO, R))
hr = w.s([hrp], 'rpred', '( ph -> H e. RR )')
c128 = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; ; 1 2 8 e. NN0')], 'nn0rei', '; ; 1 2 8 e. RR')
kh = w.s([w.s([c128], 'a1i', '( ph -> ; ; 1 2 8 e. RR )'), hr], 'remulcld', '( ph -> ( ; ; 1 2 8 x. H ) e. RR )')
khc = w.s([kh], 'recnd', '( ph -> ( ; ; 1 2 8 x. H ) e. CC )')
rc = w.s([rrp], 'rpcnd', '( %s -> %s e. CC )' % (AU, R))
iblm = w.s([khc, rc, ibl0], 'iblmulc2', '( ph -> ( u e. %s |-> %s ) e. L^1 )' % (XO, MJ))
le = w.s(['4', iblm, gmlr, mjr, ptw], 'itgle', '( ph -> S. %s %s _d u <_ S. %s %s _d u )' % (XO, GML, XO, MJ))
mul = w.s([w.s([khc, rc, ibl0], 'itgmulc2', '( ph -> ( ( ; ; 1 2 8 x. H ) x. S. %s %s _d u ) = S. %s %s _d u )' % (XO, R, XO, MJ))], 'eqcomd', '( ph -> S. %s %s _d u = ( ( ; ; 1 2 8 x. H ) x. S. %s %s _d u ) )' % (XO, MJ, XO, R))
rr = w.s([rrp], 'rpred', '( %s -> %s e. RR )' % (AU, R))
irr = w.s([rr, ibl0], 'itgrecl', '( ph -> S. %s %s _d u e. RR )' % (XO, R))
eightr = w.s([a1(w, P, '8re', '8 e. RR'), l2rp], 'rerpdivcld', '( ph -> %s e. RR )' % EIGHTL)
c1280 = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; ; 1 2 8 e. NN0')], 'nn0ge0i', '0 <_ ; ; 1 2 8')
kh0 = w.s([w.s([c128], 'a1i', '( ph -> ; ; 1 2 8 e. RR )'), hr, w.s([c1280], 'a1i', '( ph -> 0 <_ ; ; 1 2 8 )'), w.s([hrp], 'rpge0d', '( ph -> 0 <_ H )')], 'mulge0d', '( ph -> 0 <_ ( ; ; 1 2 8 x. H ) )')
bnd = w.s([irr, eightr, kh, kh0, w.s(['2', w.inst('exp4itg2')], 'syl', '( ph -> S. %s %s _d u <_ %s )' % (XO, R, EIGHTL))], 'lemul2ad', '( ph -> ( ( ; ; 1 2 8 x. H ) x. S. %s %s _d u ) <_ ( ( ; ; 1 2 8 x. H ) x. %s ) )' % (XO, R, EIGHTL))
C1024 = '; ; ; 1 0 2 4'
FIN = '( ( %s x. H ) / %s )' % (C1024, L2)
cl.have('( ; ; 1 2 8 x. H )', 'RR', kh)
alg = w.s([w.s([w.s([khc, a1(w, P, '8cn', '8 e. CC'), w.s([l2r], 'recnd', '( ph -> %s e. CC )' % L2), w.s([l2rp], 'rpne0d', '( ph -> %s =/= 0 )' % L2)], 'divassd',
                    '( ph -> ( ( ( ; ; 1 2 8 x. H ) x. 8 ) / %s ) = ( ( ; ; 1 2 8 x. H ) x. %s ) )' % (L2, EIGHTL))], 'eqcomd', '( ph -> ( ( ; ; 1 2 8 x. H ) x. %s ) = ( ( ( ; ; 1 2 8 x. H ) x. 8 ) / %s ) )' % (EIGHTL, L2)),
           w.s([lineq(w, P, '( ( ; ; 1 2 8 x. H ) x. 8 )', '( %s x. H )' % C1024, closure=cl)], 'oveq1d', '( ph -> ( ( ( ; ; 1 2 8 x. H ) x. 8 ) / %s ) = %s )' % (L2, FIN))], 'eqtrd',
          '( ph -> ( ( ; ; 1 2 8 x. H ) x. %s ) = %s )' % (EIGHTL, FIN))
finr = w.s([w.s([w.s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; ; 1 0 2 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '%s e. NN0' % C1024)], 'nn0rei', '%s e. RR' % C1024)], 'a1i', '( ph -> %s e. RR )' % C1024), hr], 'remulcld', '( ph -> ( %s x. H ) e. RR )' % C1024)
finr2 = w.s([finr, l2rp], 'rerpdivcld', '( ph -> %s e. RR )' % FIN)
igr = w.s([gmlr, '4'], 'itgrecl', '( ph -> S. %s %s _d u e. RR )' % (XO, GML))
imr = w.s([mjr, iblm], 'itgrecl', '( ph -> S. %s %s _d u e. RR )' % (XO, MJ))
w.qed([igr, imr, finr2, le, w.s([mul, w.s([bnd, alg], 'breqtrd', '( ph -> ( ( ; ; 1 2 8 x. H ) x. S. %s %s _d u ) <_ %s )' % (XO, R, FIN))], 'eqbrtrd', '( ph -> S. %s %s _d u <_ %s )' % (XO, MJ, FIN))], 'letrd',
      '( ph -> S. %s %s _d u <_ %s )' % (XO, GML, FIN))
run7(w, h=True)
