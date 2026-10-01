"""C7, Perron block 6: the vertical-edge log bounds and the trivial-regime kernel bound
(pkvlog, pkvlogn, pkbnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq

X = '( 0 (,) 1 )'
XC = '( 0 [,] 1 )'
K = '( Q - P )'
UC = '( U ^c C )'
PQ = '( P e. RR+ /\\ Q e. RR+ )'


def WT(t):
    return '( P + ( %s x. %s ) )' % (t, K)


def LQ(t):
    return '( ( Q - P ) / %s )' % WT(t)


def vctx(w, A0, order):
    """U C P Q facts under A0 = ( ( U e. RR+ /\\ C e. RR+ ) /\\ ( PQ /\\ order ) )"""
    d = {}
    d['urp'] = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0)
    d['crp'] = w.s([], 'simplr', '( %s -> C e. RR+ )' % A0)
    d['prp'] = w.s([], 'simprll', '( %s -> P e. RR+ )' % A0)
    d['qrp'] = w.s([], 'simprlr', '( %s -> Q e. RR+ )' % A0)
    d['ord'] = w.s([], 'simprr', '( %s -> %s )' % (A0, order))
    cl = Closure(w, A0, {'U': ('RR+', d['urp']), 'C': ('RR+', d['crp']), 'P': ('RR+', d['prp']), 'Q': ('RR+', d['qrp'])})
    d['cl'] = cl
    d['ucrp'] = w.s([d['urp'], cl.mem('C', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UC))
    cl.have(UC, 'RR+', d['ucrp']); cl.atom(UC)
    d['cne'] = w.s([d['crp']], 'rpne0d', '( %s -> C =/= 0 )' % A0)
    d['fcn'] = pkfcn_(w, A0, d['urp'])
    return d


def wwform(w, AT, A, B, C_, S1, S2, cc, s1c, s2c, tc, ii):
    """under AT (t e. X): ( ( A + ( t x. ( B - A ) ) ) = CPT(C, ( S1 + ( t x. ( S2 - S1 ) ) ) ) )
    with A = CPT(C,S1), B = CPT(C,S2); ii: ( AT -> _i e. CC )"""
    dif = vdiff(w, AT, C_, S1, S2, cc, s1c, s2c)
    KK = '( %s - %s )' % (S2, S1)
    kk = w.s([s2c, s1c], 'subcld', '( %s -> %s e. CC )' % (AT, KK))
    m = w.s([tc, ii, kk], 'mul12d', '( %s -> ( t x. ( _i x. %s ) ) = ( _i x. ( t x. %s ) ) )' % (AT, KK, KK))
    e1 = w.s([w.s([dif], 'oveq2d', '( %s -> ( t x. ( %s - %s ) ) = ( t x. ( _i x. %s ) ) )' % (AT, B, A, KK)), m], 'eqtrd',
             '( %s -> ( t x. ( %s - %s ) ) = ( _i x. ( t x. %s ) ) )' % (AT, B, A, KK))
    e2 = w.s([e1], 'oveq2d', '( %s -> ( %s + ( t x. ( %s - %s ) ) ) = ( %s + ( _i x. ( t x. %s ) ) ) )' % (AT, A, B, A, A, KK))
    is1 = w.s([ii, s1c], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (AT, S1))
    tk = w.s([tc, kk], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (AT, KK))
    itk = w.s([ii, tk], 'mulcld', '( %s -> ( _i x. ( t x. %s ) ) e. CC )' % (AT, KK))
    e3 = w.s([cc, is1, itk], 'addassd', '( %s -> ( ( %s + ( _i x. %s ) ) + ( _i x. ( t x. %s ) ) ) = ( %s + ( ( _i x. %s ) + ( _i x. ( t x. %s ) ) ) ) )' % (AT, C_, S1, KK, C_, S1, KK))
    e4 = w.s([w.s([ii, s1c, tk], 'adddid', '( %s -> ( _i x. ( %s + ( t x. %s ) ) ) = ( ( _i x. %s ) + ( _i x. ( t x. %s ) ) ) )' % (AT, S1, KK, S1, KK))], 'eqcomd',
             '( %s -> ( ( _i x. %s ) + ( _i x. ( t x. %s ) ) ) = ( _i x. ( %s + ( t x. %s ) ) ) )' % (AT, S1, KK, S1, KK))
    e5 = w.s([e3, w.s([e4], 'oveq2d', '( %s -> ( %s + ( ( _i x. %s ) + ( _i x. ( t x. %s ) ) ) ) = ( %s + ( _i x. ( %s + ( t x. %s ) ) ) ) )' % (AT, C_, S1, KK, C_, S1, KK))], 'eqtrd',
             '( %s -> ( ( %s + ( _i x. %s ) ) + ( _i x. ( t x. %s ) ) ) = ( %s + ( _i x. ( %s + ( t x. %s ) ) ) ) )' % (AT, C_, S1, KK, C_, S1, KK))
    return w.s([e2, e5], 'eqtrd', '( %s -> ( %s + ( t x. ( %s - %s ) ) ) = %s )' % (AT, A, B, A, CPT(C_, '( %s + ( t x. %s ) )' % (S1, KK)))), dif


# ---------------------------------------------------------------- pkvlog
A0 = '( ( U e. RR+ /\\ C e. RR+ ) /\\ ( %s /\\ P <_ Q ) )' % PQ
w = W('pkvlog', 'The vertical-edge log bound for the Perron integrand: on the segment of the '
      'line ` Re = C ` from height ` P ` to height ` Q `, ` 0 < P <_ Q `, the modulus of the '
      'integrand is at most ` ( U ^c C ) / y ` at height ` y ` and the majorant integrates to '
      '` ( U ^c C ) ( log Q - log P ) ` ( ~ lintle , ~ logaffitg ).')
d = vctx(w, A0, 'P <_ Q'); cl = d['cl']
cr = cl.mem('C', 'RR'); pr = cl.mem('P', 'RR'); qr = cl.mem('Q', 'RR'); kr = cl.mem(K, 'RR')
cc = w.s([cr], 'recnd', '( %s -> C e. CC )' % A0); pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0); qc = w.s([qr], 'recnd', '( %s -> Q e. CC )' % A0)
kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A0, K))
k0 = linarith(w, A0, [d['ord']], '0 <_ %s' % K, closure=cl)
A = CPT('C', 'P'); B = CPT('C', 'Q')
ac = cptcl(w, A0, 'C', 'P', cr, pr); bc = cptcl(w, A0, 'C', 'Q', cr, qr)
ss = segv(w, A0, 'C', 'P', 'Q', cr, d['cne'], pr, qr)
AT = '( %s /\\ t e. %s )' % (A0, X)
tio = w.s([], 'simpr', '( %s -> t e. %s )' % (AT, X))
tr = w.s([a1(w, AT, 'ioossre', '%s C_ RR' % X), tio], 'sseldd', '( %s -> t e. RR )' % AT)
tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % AT)
t01 = w.s([a1(w, AT, 'ioossicc', '%s C_ %s' % (X, XC)), tio], 'sseldd', '( %s -> t e. %s )' % (AT, XC))
ii = a1(w, AT, 'ax-icn', '_i e. CC')
cct = w.s([cc], 'adantr', '( %s -> C e. CC )' % AT); pct = w.s([pc], 'adantr', '( %s -> P e. CC )' % AT); qct = w.s([qc], 'adantr', '( %s -> Q e. CC )' % AT)
WW = '( %s + ( t x. ( %s - %s ) ) )' % (A, B, A)
wweq, dif = wwform(w, AT, A, B, 'C', 'P', 'Q', cct, pct, qct, tc, ii)
# WT(t) e. RR+
prpt = w.s([d['prp']], 'adantr', '( %s -> P e. RR+ )' % AT); qrpt = w.s([d['qrp']], 'adantr', '( %s -> Q e. RR+ )' % AT)
pos = w.s([w.s([w.s([prpt, qrpt], 'jca', '( %s -> %s )' % (AT, PQ)), t01], 'jca', '( %s -> ( %s /\\ t e. %s ) )' % (AT, PQ, XC)), w.inst('affpos')], 'syl', '( %s -> 0 < %s )' % (AT, WT('t')))
wtr = w.s([w.s([pr], 'adantr', '( %s -> P e. RR )' % AT), w.s([tr, w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K))], 'remulcld', '( %s -> ( t x. %s ) e. RR )' % (AT, K))], 'readdcld',
          '( %s -> %s e. RR )' % (AT, WT('t')))
wrp = w.s([wtr, pos], 'elrpd', '( %s -> %s e. RR+ )' % (AT, WT('t')))
crt = w.s([cr], 'adantr', '( %s -> C e. RR )' % AT)
rew = w.s([w.s([wweq], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (AT, WW, CPT('C', WT('t')))), w.s([crt, wtr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = C )' % (AT, CPT('C', WT('t'))))],
          'eqtrd', '( %s -> ( Re ` %s ) = C )' % (AT, WW))
imw = w.s([w.s([wweq], 'fveq2d', '( %s -> ( Im ` %s ) = ( Im ` %s ) )' % (AT, WW, CPT('C', WT('t')))), w.s([crt, wtr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (AT, CPT('C', WT('t')), WT('t')))],
          'eqtrd', '( %s -> ( Im ` %s ) = %s )' % (AT, WW, WT('t')))
# WW in the punctured plane
wseg = w.s([w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AT, A)), w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AT, B)), t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( %s cseg %s ) )' % (AT, WW, A, B))
wd = w.s([w.s([ss], 'adantr', '( %s -> ( %s cseg %s ) C_ %s )' % (AT, A, B, DOM)), wseg], 'sseldd', '( %s -> %s e. %s )' % (AT, WW, DOM))
wc = w.s([wd, w.inst('eldifi')], 'syl', '( %s -> %s e. CC )' % (AT, WW))
wne = w.s([wd, w.inst('eldifsni')], 'syl', '( %s -> %s =/= 0 )' % (AT, WW))
urpt = w.s([d['urp']], 'adantr', '( %s -> U e. RR+ )' % AT)
pkv = w.s([w.s([urpt, wd], 'jca', '( %s -> ( U e. RR+ /\\ %s e. %s ) )' % (AT, WW, DOM)), w.inst('pkfval')], 'syl',
          '( %s -> ( abs ` ( %s ` %s ) ) = ( ( U ^c ( Re ` %s ) ) / ( abs ` %s ) ) )' % (AT, PK0, WW, WW, WW))
pkv2 = w.s([pkv, w.s([w.s([rew], 'oveq2d', '( %s -> ( U ^c ( Re ` %s ) ) = %s )' % (AT, WW, UC))], 'oveq1d', '( %s -> ( ( U ^c ( Re ` %s ) ) / ( abs ` %s ) ) = ( %s / ( abs ` %s ) ) )' % (AT, WW, WW, UC, WW))],
           'eqtrd', '( %s -> ( abs ` ( %s ` %s ) ) = ( %s / ( abs ` %s ) ) )' % (AT, PK0, WW, UC, WW))
pkfv = w.s([w.s([d['fcn']], 'adantr', '( %s -> %s e. ( %s -cn-> CC ) )' % (AT, PK0, DOM)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (AT, PK0, DOM))
pkcl = w.s([pkfv, wd], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (AT, PK0, WW))
difc = w.s([w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AT, B)), w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AT, A))], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (AT, B, A))
INTG = '( ( %s ` %s ) x. ( %s - %s ) )' % (PK0, WW, B, A)
absi = w.s([pkcl, difc], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` ( %s ` %s ) ) x. ( abs ` ( %s - %s ) ) ) )' % (AT, INTG, PK0, WW, B, A))
absd = w.s([w.s([w.s([dif], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. %s ) ) )' % (AT, B, A, K)), absi_(w, AT, K, w.s([kc], 'adantr', '( %s -> %s e. CC )' % (AT, K)))], 'eqtrd',
                '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` %s ) )' % (AT, B, A, K)),
           w.s([w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K)), w.s([k0], 'adantr', '( %s -> 0 <_ %s )' % (AT, K))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (AT, K, K))], 'eqtrd',
          '( %s -> ( abs ` ( %s - %s ) ) = %s )' % (AT, B, A, K))
absi2 = w.s([absi, w.s([pkv2, absd], 'oveq12d', '( %s -> ( ( abs ` ( %s ` %s ) ) x. ( abs ` ( %s - %s ) ) ) = ( ( %s / ( abs ` %s ) ) x. %s ) )' % (AT, PK0, WW, B, A, UC, WW, K))], 'eqtrd',
            '( %s -> ( abs ` %s ) = ( ( %s / ( abs ` %s ) ) x. %s ) )' % (AT, INTG, UC, WW, K))
absw = w.s([wc, wne], 'absrpcld', '( %s -> ( abs ` %s ) e. RR+ )' % (AT, WW))
lew = w.s([w.s([w.s([w.s([imw], 'fveq2d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` %s ) )' % (AT, WW, WT('t'))), w.s([wtr, w.s([wrp], 'rpge0d', '( %s -> 0 <_ %s )' % (AT, WT('t')))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (AT, WT('t'), WT('t')))],
                    'eqtrd', '( %s -> ( abs ` ( Im ` %s ) ) = %s )' % (AT, WW, WT('t')))], 'eqcomd', '( %s -> %s = ( abs ` ( Im ` %s ) ) )' % (AT, WT('t'), WW)),
           w.s([wc, w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` %s ) ) <_ ( abs ` %s ) )' % (AT, WW, WW))], 'eqbrtrd', '( %s -> %s <_ ( abs ` %s ) )' % (AT, WT('t'), WW))
ucrpt = w.s([d['ucrp']], 'adantr', '( %s -> %s e. RR+ )' % (AT, UC))
dle = w.s([wrp, absw, w.s([ucrpt], 'rpred', '( %s -> %s e. RR )' % (AT, UC)), w.s([ucrpt], 'rpge0d', '( %s -> 0 <_ %s )' % (AT, UC)), lew], 'lediv2ad',
          '( %s -> ( %s / ( abs ` %s ) ) <_ ( %s / %s ) )' % (AT, UC, WW, UC, WT('t')))
q1r = w.s([w.s([ucrpt, absw], 'rpdivcld', '( %s -> ( %s / ( abs ` %s ) ) e. RR+ )' % (AT, UC, WW))], 'rpred', '( %s -> ( %s / ( abs ` %s ) ) e. RR )' % (AT, UC, WW))
q2r = w.s([w.s([ucrpt, wrp], 'rpdivcld', '( %s -> ( %s / %s ) e. RR+ )' % (AT, UC, WT('t')))], 'rpred', '( %s -> ( %s / %s ) e. RR )' % (AT, UC, WT('t')))
mle = w.s([q1r, q2r, w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K)), w.s([k0], 'adantr', '( %s -> 0 <_ %s )' % (AT, K)), dle], 'lemul1ad',
          '( %s -> ( ( %s / ( abs ` %s ) ) x. %s ) <_ ( ( %s / %s ) x. %s ) )' % (AT, UC, WW, K, UC, WT('t'), K))
H = '( %s x. %s )' % (UC, LQ('t'))
ucct = w.s([ucrpt], 'rpcnd', '( %s -> %s e. CC )' % (AT, UC)); kct = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (AT, K))
wct = w.s([wrp], 'rpcnd', '( %s -> %s e. CC )' % (AT, WT('t'))); wnet = w.s([wrp], 'rpne0d', '( %s -> %s =/= 0 )' % (AT, WT('t')))
alg = w.s([w.s([w.s([ucct, kct, wct, wnet], 'div23d', '( %s -> ( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s ) )' % (AT, UC, K, WT('t'), UC, WT('t'), K))], 'eqcomd',
               '( %s -> ( ( %s / %s ) x. %s ) = ( ( %s x. %s ) / %s ) )' % (AT, UC, WT('t'), K, UC, K, WT('t'))),
           w.s([ucct, kct, wct, wnet], 'divassd', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (AT, UC, K, WT('t'), H))], 'eqtrd',
          '( %s -> ( ( %s / %s ) x. %s ) = %s )' % (AT, UC, WT('t'), K, H))
ptw = w.s([absi2, w.s([mle, alg], 'breqtrd', '( %s -> ( ( %s / ( abs ` %s ) ) x. %s ) <_ %s )' % (AT, UC, WW, K, H))], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (AT, INTG, H))
lqr = w.s([w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K)), wrp], 'rerpdivcld', '( %s -> %s e. RR )' % (AT, LQ('t')))
hrr = w.s([w.s([ucrpt], 'rpred', '( %s -> %s e. RR )' % (AT, UC)), lqr], 'remulcld', '( %s -> %s e. RR )' % (AT, H))
ibl = w.s([w.s([d['prp'], d['qrp']], 'jca', '( %s -> %s )' % (A0, PQ)), w.inst('logaffibl')], 'syl', '( %s -> ( ( t e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( t e. %s |-> %s ) e. L^1 ) )' % (A0, X, LQ('t'), X, X, LQ('t')))
lqibl = w.s([ibl, w.inst('simpr')], 'syl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, X, LQ('t')))
lqc = w.s([lqr], 'recnd', '( %s -> %s e. CC )' % (AT, LQ('t')))
ucc = w.s([d['ucrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC))
hibl = w.s([ucc, lqc, lqibl], 'iblmulc2', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, X, H))
le = w.s([ac, bc, d['fcn'], ss, hibl, hrr, ptw], 'lintle', '( %s -> ( abs ` %s ) <_ S. %s %s _d t )' % (A0, E(A, B), X, H))
itgv = w.s([ucc, lqc, lqibl], 'itgmulc2', '( %s -> ( %s x. S. %s %s _d t ) = S. %s %s _d t )' % (A0, UC, X, LQ('t'), X, H))
aitg = w.s([w.s([d['prp'], d['qrp']], 'jca', '( %s -> %s )' % (A0, PQ)), w.inst('logaffitg')], 'syl', '( %s -> S. %s %s _d t = ( ( log ` Q ) - ( log ` P ) ) )' % (A0, X, LQ('t')))
w.qed([le, w.s([w.s([itgv], 'eqcomd', '( %s -> S. %s %s _d t = ( %s x. S. %s %s _d t ) )' % (A0, X, H, UC, X, LQ('t'))),
                w.s([aitg], 'oveq2d', '( %s -> ( %s x. S. %s %s _d t ) = ( %s x. ( ( log ` Q ) - ( log ` P ) ) ) )' % (A0, UC, X, LQ('t'), UC))], 'eqtrd',
               '( %s -> S. %s %s _d t = ( %s x. ( ( log ` Q ) - ( log ` P ) ) ) )' % (A0, X, H, UC))], 'breqtrd',
      '( %s -> ( abs ` %s ) <_ ( %s x. ( ( log ` Q ) - ( log ` P ) ) ) )' % (A0, E(A, B), UC))
run7(w)

# ---------------------------------------------------------------- pkvlogn
A0 = '( ( U e. RR+ /\\ C e. RR+ ) /\\ ( %s /\\ Q <_ P ) )' % PQ
KN = '( P - Q )'
w = W('pkvlogn', 'The vertical-edge log bound for the Perron integrand below the real axis: '
      'on the segment of the line ` Re = C ` from height ` -u P ` to height ` -u Q `, '
      '` 0 < Q <_ P `, the majorant integrates to ` ( U ^c C ) ( log P - log Q ) ` '
      '( ~ lintle , ~ logaffitg , ~ itgneg ).')
d = vctx(w, A0, 'Q <_ P'); cl = d['cl']
cr = cl.mem('C', 'RR'); pr = cl.mem('P', 'RR'); qr = cl.mem('Q', 'RR'); kr = cl.mem(K, 'RR'); knr = cl.mem(KN, 'RR')
cc = w.s([cr], 'recnd', '( %s -> C e. CC )' % A0); pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0); qc = w.s([qr], 'recnd', '( %s -> Q e. CC )' % A0)
kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A0, K)); knc = w.s([knr], 'recnd', '( %s -> %s e. CC )' % (A0, KN))
kn0 = linarith(w, A0, [d['ord']], '0 <_ %s' % KN, closure=cl)
npr = cl.mem('-u P', 'RR'); nqr = cl.mem('-u Q', 'RR')
A = CPT('C', '-u P'); B = CPT('C', '-u Q')
ac = cptcl(w, A0, 'C', '-u P', cr, npr); bc = cptcl(w, A0, 'C', '-u Q', cr, nqr)
ss = segv(w, A0, 'C', '-u P', '-u Q', cr, d['cne'], npr, nqr)
AT = '( %s /\\ t e. %s )' % (A0, X)
tio = w.s([], 'simpr', '( %s -> t e. %s )' % (AT, X))
tr = w.s([a1(w, AT, 'ioossre', '%s C_ RR' % X), tio], 'sseldd', '( %s -> t e. RR )' % AT)
tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % AT)
t01 = w.s([a1(w, AT, 'ioossicc', '%s C_ %s' % (X, XC)), tio], 'sseldd', '( %s -> t e. %s )' % (AT, XC))
ii = a1(w, AT, 'ax-icn', '_i e. CC')
cct = w.s([cc], 'adantr', '( %s -> C e. CC )' % AT); pct = w.s([pc], 'adantr', '( %s -> P e. CC )' % AT); qct = w.s([qc], 'adantr', '( %s -> Q e. CC )' % AT)
npc = w.s([pct], 'negcld', '( %s -> -u P e. CC )' % AT); nqc = w.s([qct], 'negcld', '( %s -> -u Q e. CC )' % AT)
WW = '( %s + ( t x. ( %s - %s ) ) )' % (A, B, A)
wweq, dif = wwform(w, AT, A, B, 'C', '-u P', '-u Q', cct, npc, nqc, tc, ii)
IMT = '( -u P + ( t x. ( -u Q - -u P ) ) )'
# IMT = -u WT(t)
n2s = w.s([qct, pct], 'neg2subd', '( %s -> ( -u Q - -u P ) = %s )' % (AT, KN))
cl_t = Closure(w, AT, {'P': ('RR', w.s([pr], 'adantr', '( %s -> P e. RR )' % AT)), 'Q': ('RR', w.s([qr], 'adantr', '( %s -> Q e. RR )' % AT)), 't': ('RR', tr)})
kct_ = w.s([qct, pct], 'subcld', '( %s -> %s e. CC )' % (AT, K))
tk_ = w.s([tc, kct_], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (AT, K))
nw1 = w.s([pct, tk_], 'negdid', '( %s -> -u %s = ( -u P + -u ( t x. %s ) ) )' % (AT, WT('t'), K))
nw2 = w.s([w.s([w.s([tc, kct_], 'mulneg2d', '( %s -> ( t x. -u %s ) = -u ( t x. %s ) )' % (AT, K, K))], 'eqcomd', '( %s -> -u ( t x. %s ) = ( t x. -u %s ) )' % (AT, K, K)),
           w.s([w.s([qct, pct], 'negsubdi2d', '( %s -> -u %s = %s )' % (AT, K, KN))], 'oveq2d', '( %s -> ( t x. -u %s ) = ( t x. %s ) )' % (AT, K, KN))], 'eqtrd',
          '( %s -> -u ( t x. %s ) = ( t x. %s ) )' % (AT, K, KN))
nweq = w.s([nw1, w.s([nw2], 'oveq2d', '( %s -> ( -u P + -u ( t x. %s ) ) = ( -u P + ( t x. %s ) ) )' % (AT, K, KN))], 'eqtrd', '( %s -> -u %s = ( -u P + ( t x. %s ) ) )' % (AT, WT('t'), KN))
imeq = w.s([w.s([w.s([n2s], 'oveq2d', '( %s -> ( t x. ( -u Q - -u P ) ) = ( t x. %s ) )' % (AT, KN))], 'oveq2d', '( %s -> %s = ( -u P + ( t x. %s ) ) )' % (AT, IMT, KN)),
            w.s([nweq], 'eqcomd', '( %s -> ( -u P + ( t x. %s ) ) = -u %s )' % (AT, KN, WT('t')))], 'eqtrd', '( %s -> %s = -u %s )' % (AT, IMT, WT('t')))
prpt = w.s([d['prp']], 'adantr', '( %s -> P e. RR+ )' % AT); qrpt = w.s([d['qrp']], 'adantr', '( %s -> Q e. RR+ )' % AT)
pos = w.s([w.s([w.s([prpt, qrpt], 'jca', '( %s -> %s )' % (AT, PQ)), t01], 'jca', '( %s -> ( %s /\\ t e. %s ) )' % (AT, PQ, XC)), w.inst('affpos')], 'syl', '( %s -> 0 < %s )' % (AT, WT('t')))
wtr = cl_t.mem(WT('t'), 'RR')
wrp = w.s([wtr, pos], 'elrpd', '( %s -> %s e. RR+ )' % (AT, WT('t')))
nwtr = w.s([wtr], 'renegcld', '( %s -> -u %s e. RR )' % (AT, WT('t')))
crt = w.s([cr], 'adantr', '( %s -> C e. RR )' % AT)
wweq2 = w.s([wweq, w.s([w.s([imeq], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. -u %s ) )' % (AT, IMT, WT('t')))], 'oveq2d', '( %s -> %s = %s )' % (AT, CPT('C', IMT), CPT('C', '-u ' + WT('t'))))],
           'eqtrd', '( %s -> %s = %s )' % (AT, WW, CPT('C', '-u ' + WT('t'))))
rew = w.s([w.s([wweq2], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (AT, WW, CPT('C', '-u ' + WT('t')))), w.s([crt, nwtr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = C )' % (AT, CPT('C', '-u ' + WT('t'))))],
          'eqtrd', '( %s -> ( Re ` %s ) = C )' % (AT, WW))
imw = w.s([w.s([wweq2], 'fveq2d', '( %s -> ( Im ` %s ) = ( Im ` %s ) )' % (AT, WW, CPT('C', '-u ' + WT('t')))), w.s([crt, nwtr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = -u %s )' % (AT, CPT('C', '-u ' + WT('t')), WT('t')))],
          'eqtrd', '( %s -> ( Im ` %s ) = -u %s )' % (AT, WW, WT('t')))
wseg = w.s([w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AT, A)), w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AT, B)), t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( %s cseg %s ) )' % (AT, WW, A, B))
wd = w.s([w.s([ss], 'adantr', '( %s -> ( %s cseg %s ) C_ %s )' % (AT, A, B, DOM)), wseg], 'sseldd', '( %s -> %s e. %s )' % (AT, WW, DOM))
wc = w.s([wd, w.inst('eldifi')], 'syl', '( %s -> %s e. CC )' % (AT, WW))
wne = w.s([wd, w.inst('eldifsni')], 'syl', '( %s -> %s =/= 0 )' % (AT, WW))
urpt = w.s([d['urp']], 'adantr', '( %s -> U e. RR+ )' % AT)
pkv = w.s([w.s([urpt, wd], 'jca', '( %s -> ( U e. RR+ /\\ %s e. %s ) )' % (AT, WW, DOM)), w.inst('pkfval')], 'syl',
          '( %s -> ( abs ` ( %s ` %s ) ) = ( ( U ^c ( Re ` %s ) ) / ( abs ` %s ) ) )' % (AT, PK0, WW, WW, WW))
pkv2 = w.s([pkv, w.s([w.s([rew], 'oveq2d', '( %s -> ( U ^c ( Re ` %s ) ) = %s )' % (AT, WW, UC))], 'oveq1d', '( %s -> ( ( U ^c ( Re ` %s ) ) / ( abs ` %s ) ) = ( %s / ( abs ` %s ) ) )' % (AT, WW, WW, UC, WW))],
           'eqtrd', '( %s -> ( abs ` ( %s ` %s ) ) = ( %s / ( abs ` %s ) ) )' % (AT, PK0, WW, UC, WW))
pkfv = w.s([w.s([d['fcn']], 'adantr', '( %s -> %s e. ( %s -cn-> CC ) )' % (AT, PK0, DOM)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (AT, PK0, DOM))
pkcl = w.s([pkfv, wd], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (AT, PK0, WW))
difc = w.s([w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AT, B)), w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AT, A))], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (AT, B, A))
INTG = '( ( %s ` %s ) x. ( %s - %s ) )' % (PK0, WW, B, A)
absi = w.s([pkcl, difc], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` ( %s ` %s ) ) x. ( abs ` ( %s - %s ) ) ) )' % (AT, INTG, PK0, WW, B, A))
dif2 = w.s([dif, w.s([n2s], 'oveq2d', '( %s -> ( _i x. ( -u Q - -u P ) ) = ( _i x. %s ) )' % (AT, KN))], 'eqtrd', '( %s -> ( %s - %s ) = ( _i x. %s ) )' % (AT, B, A, KN))
knct = w.s([knc], 'adantr', '( %s -> %s e. CC )' % (AT, KN))
absd = w.s([w.s([w.s([dif2], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. %s ) ) )' % (AT, B, A, KN)), absi_(w, AT, KN, knct)], 'eqtrd',
                '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` %s ) )' % (AT, B, A, KN)),
           w.s([w.s([knr], 'adantr', '( %s -> %s e. RR )' % (AT, KN)), w.s([kn0], 'adantr', '( %s -> 0 <_ %s )' % (AT, KN))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (AT, KN, KN))], 'eqtrd',
          '( %s -> ( abs ` ( %s - %s ) ) = %s )' % (AT, B, A, KN))
absi2 = w.s([absi, w.s([pkv2, absd], 'oveq12d', '( %s -> ( ( abs ` ( %s ` %s ) ) x. ( abs ` ( %s - %s ) ) ) = ( ( %s / ( abs ` %s ) ) x. %s ) )' % (AT, PK0, WW, B, A, UC, WW, KN))], 'eqtrd',
            '( %s -> ( abs ` %s ) = ( ( %s / ( abs ` %s ) ) x. %s ) )' % (AT, INTG, UC, WW, KN))
absw = w.s([wc, wne], 'absrpcld', '( %s -> ( abs ` %s ) e. RR+ )' % (AT, WW))
absn = w.s([w.s([w.s([wtr], 'recnd', '( %s -> %s e. CC )' % (AT, WT('t')))], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (AT, WT('t'), WT('t'))),
            w.s([wtr, w.s([wrp], 'rpge0d', '( %s -> 0 <_ %s )' % (AT, WT('t')))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (AT, WT('t'), WT('t')))], 'eqtrd',
           '( %s -> ( abs ` -u %s ) = %s )' % (AT, WT('t'), WT('t')))
lew = w.s([w.s([w.s([w.s([imw], 'fveq2d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` -u %s ) )' % (AT, WW, WT('t'))), absn], 'eqtrd', '( %s -> ( abs ` ( Im ` %s ) ) = %s )' % (AT, WW, WT('t')))], 'eqcomd',
                '( %s -> %s = ( abs ` ( Im ` %s ) ) )' % (AT, WT('t'), WW)),
           w.s([wc, w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` %s ) ) <_ ( abs ` %s ) )' % (AT, WW, WW))], 'eqbrtrd', '( %s -> %s <_ ( abs ` %s ) )' % (AT, WT('t'), WW))
ucrpt = w.s([d['ucrp']], 'adantr', '( %s -> %s e. RR+ )' % (AT, UC))
dle = w.s([wrp, absw, w.s([ucrpt], 'rpred', '( %s -> %s e. RR )' % (AT, UC)), w.s([ucrpt], 'rpge0d', '( %s -> 0 <_ %s )' % (AT, UC)), lew], 'lediv2ad',
          '( %s -> ( %s / ( abs ` %s ) ) <_ ( %s / %s ) )' % (AT, UC, WW, UC, WT('t')))
q1r = w.s([w.s([ucrpt, absw], 'rpdivcld', '( %s -> ( %s / ( abs ` %s ) ) e. RR+ )' % (AT, UC, WW))], 'rpred', '( %s -> ( %s / ( abs ` %s ) ) e. RR )' % (AT, UC, WW))
q2r = w.s([w.s([ucrpt, wrp], 'rpdivcld', '( %s -> ( %s / %s ) e. RR+ )' % (AT, UC, WT('t')))], 'rpred', '( %s -> ( %s / %s ) e. RR )' % (AT, UC, WT('t')))
mle = w.s([q1r, q2r, w.s([knr], 'adantr', '( %s -> %s e. RR )' % (AT, KN)), w.s([kn0], 'adantr', '( %s -> 0 <_ %s )' % (AT, KN)), dle], 'lemul1ad',
          '( %s -> ( ( %s / ( abs ` %s ) ) x. %s ) <_ ( ( %s / %s ) x. %s ) )' % (AT, UC, WW, KN, UC, WT('t'), KN))
LN = '( %s / %s )' % (KN, WT('t'))
H = '( %s x. %s )' % (UC, LN)
ucct = w.s([ucrpt], 'rpcnd', '( %s -> %s e. CC )' % (AT, UC))
wct = w.s([wrp], 'rpcnd', '( %s -> %s e. CC )' % (AT, WT('t'))); wnet = w.s([wrp], 'rpne0d', '( %s -> %s =/= 0 )' % (AT, WT('t')))
alg = w.s([w.s([w.s([ucct, knct, wct, wnet], 'div23d', '( %s -> ( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s ) )' % (AT, UC, KN, WT('t'), UC, WT('t'), KN))], 'eqcomd',
               '( %s -> ( ( %s / %s ) x. %s ) = ( ( %s x. %s ) / %s ) )' % (AT, UC, WT('t'), KN, UC, KN, WT('t'))),
           w.s([ucct, knct, wct, wnet], 'divassd', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (AT, UC, KN, WT('t'), H))], 'eqtrd',
          '( %s -> ( ( %s / %s ) x. %s ) = %s )' % (AT, UC, WT('t'), KN, H))
ptw = w.s([absi2, w.s([mle, alg], 'breqtrd', '( %s -> ( ( %s / ( abs ` %s ) ) x. %s ) <_ %s )' % (AT, UC, WW, KN, H))], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (AT, INTG, H))
lnr = w.s([w.s([knr], 'adantr', '( %s -> %s e. RR )' % (AT, KN)), wrp], 'rerpdivcld', '( %s -> %s e. RR )' % (AT, LN))
hrr = w.s([w.s([ucrpt], 'rpred', '( %s -> %s e. RR )' % (AT, UC)), lnr], 'remulcld', '( %s -> %s e. RR )' % (AT, H))
# LN = -u LQ, integrability and the integral
kct = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (AT, K))
lneq = w.s([w.s([w.s([w.s([qct, pct], 'negsubdi2d', '( %s -> -u %s = %s )' % (AT, K, KN))], 'eqcomd', '( %s -> %s = -u %s )' % (AT, KN, K))], 'oveq1d', '( %s -> %s = ( -u %s / %s ) )' % (AT, LN, K, WT('t'))),
            w.s([w.s([kct, wct, wnet], 'divnegd', '( %s -> -u %s = ( -u %s / %s ) )' % (AT, LQ('t'), K, WT('t')))], 'eqcomd', '( %s -> ( -u %s / %s ) = -u %s )' % (AT, K, WT('t'), LQ('t')))], 'eqtrd',
           '( %s -> %s = -u %s )' % (AT, LN, LQ('t')))
ibl = w.s([w.s([d['prp'], d['qrp']], 'jca', '( %s -> %s )' % (A0, PQ)), w.inst('logaffibl')], 'syl', '( %s -> ( ( t e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( t e. %s |-> %s ) e. L^1 ) )' % (A0, X, LQ('t'), X, X, LQ('t')))
lqibl = w.s([ibl, w.inst('simpr')], 'syl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, X, LQ('t')))
lqr = w.s([w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K)), wrp], 'rerpdivcld', '( %s -> %s e. RR )' % (AT, LQ('t')))
lqc = w.s([lqr], 'recnd', '( %s -> %s e. CC )' % (AT, LQ('t')))
nibl = w.s([lqc, lqibl], 'iblneg', '( %s -> ( t e. %s |-> -u %s ) e. L^1 )' % (A0, X, LQ('t')))
mpeq = w.s([lneq], 'mpteq2dva', '( %s -> ( t e. %s |-> %s ) = ( t e. %s |-> -u %s ) )' % (A0, X, LN, X, LQ('t')))
lnibl = w.s([mpeq, nibl], 'eqeltrd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, X, LN))
lnc = w.s([lnr], 'recnd', '( %s -> %s e. CC )' % (AT, LN))
ucc = w.s([d['ucrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC))
hibl = w.s([ucc, lnc, lnibl], 'iblmulc2', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, X, H))
le = w.s([ac, bc, d['fcn'], ss, hibl, hrr, ptw], 'lintle', '( %s -> ( abs ` %s ) <_ S. %s %s _d t )' % (A0, E(A, B), X, H))
itgv = w.s([ucc, lnc, lnibl], 'itgmulc2', '( %s -> ( %s x. S. %s %s _d t ) = S. %s %s _d t )' % (A0, UC, X, LN, X, H))
aitg = w.s([w.s([d['prp'], d['qrp']], 'jca', '( %s -> %s )' % (A0, PQ)), w.inst('logaffitg')], 'syl', '( %s -> S. %s %s _d t = ( ( log ` Q ) - ( log ` P ) ) )' % (A0, X, LQ('t')))
i1 = w.s([lneq], 'itgeq2dv', '( %s -> S. %s %s _d t = S. %s -u %s _d t )' % (A0, X, LN, X, LQ('t')))
i2 = w.s([w.s([lqc, lqibl], 'itgneg', '( %s -> -u S. %s %s _d t = S. %s -u %s _d t )' % (A0, X, LQ('t'), X, LQ('t')))], 'eqcomd', '( %s -> S. %s -u %s _d t = -u S. %s %s _d t )' % (A0, X, LQ('t'), X, LQ('t')))
lqR = w.s([d['qrp'], w.inst('relogcl')], 'syl', '( %s -> ( log ` Q ) e. RR )' % A0)
lpR = w.s([d['prp'], w.inst('relogcl')], 'syl', '( %s -> ( log ` P ) e. RR )' % A0)
i3 = w.s([w.s([aitg], 'negeqd', '( %s -> -u S. %s %s _d t = -u ( ( log ` Q ) - ( log ` P ) ) )' % (A0, X, LQ('t'))),
          w.s([w.s([lqR], 'recnd', '( %s -> ( log ` Q ) e. CC )' % A0), w.s([lpR], 'recnd', '( %s -> ( log ` P ) e. CC )' % A0)], 'negsubdi2d', '( %s -> -u ( ( log ` Q ) - ( log ` P ) ) = ( ( log ` P ) - ( log ` Q ) ) )' % A0)],
         'eqtrd', '( %s -> -u S. %s %s _d t = ( ( log ` P ) - ( log ` Q ) ) )' % (A0, X, LQ('t')))
ival = w.s([i1, w.s([i2, i3], 'eqtrd', '( %s -> S. %s -u %s _d t = ( ( log ` P ) - ( log ` Q ) ) )' % (A0, X, LQ('t')))], 'eqtrd', '( %s -> S. %s %s _d t = ( ( log ` P ) - ( log ` Q ) ) )' % (A0, X, LN))
w.qed([le, w.s([w.s([itgv], 'eqcomd', '( %s -> S. %s %s _d t = ( %s x. S. %s %s _d t ) )' % (A0, X, H, UC, X, LN)),
                w.s([ival], 'oveq2d', '( %s -> ( %s x. S. %s %s _d t ) = ( %s x. ( ( log ` P ) - ( log ` Q ) ) ) )' % (A0, UC, X, LN, UC))], 'eqtrd',
               '( %s -> S. %s %s _d t = ( %s x. ( ( log ` P ) - ( log ` Q ) ) ) )' % (A0, X, H, UC))], 'breqtrd',
      '( %s -> ( abs ` %s ) <_ ( %s x. ( ( log ` P ) - ( log ` Q ) ) ) )' % (A0, E(A, B), UC))
run7(w)

# ---------------------------------------------------------------- pkbnd
A0 = '( ( U e. RR+ /\\ C e. RR+ /\\ T e. RR+ ) /\\ C <_ T )'
M1 = CPT('C', '-u C'); M2 = CPT('C', 'C')
S1 = '( ( T - C ) / ( 2 x. T ) )'; S2 = '( ( 2 x. C ) / ( T + C ) )'
D = '( ( log ` T ) - ( log ` C ) )'
w = W('pkbnd', 'The trivial-regime bound on the truncated Perron kernel, ` C <_ T `: the kernel '
      'line is split at heights ` -u C ` and ` C ` ( ~ lintsplit ), the middle third is at most '
      '` 2 U ^c C ` ( ~ vedgbnd ) and each tail at most ` U ^c C log ( T / C ) ` ( ~ pkvlog , '
      '~ pkvlogn ).  This is ` norm_perronKernel_le ` of Route Z\'s PerronKernel.lean, '
      'times ` 2 _pi `.')
b3 = w.s([], 'simpl', '( %s -> ( U e. RR+ /\\ C e. RR+ /\\ T e. RR+ ) )' % A0)
urp = w.s([b3, w.inst('simp1')], 'syl', '( %s -> U e. RR+ )' % A0)
crp = w.s([b3, w.inst('simp2')], 'syl', '( %s -> C e. RR+ )' % A0)
trp = w.s([b3, w.inst('simp3')], 'syl', '( %s -> T e. RR+ )' % A0)
cle = w.s([], 'simpr', '( %s -> C <_ T )' % A0)
cl = Closure(w, A0, {'U': ('RR+', urp), 'C': ('RR+', crp), 'T': ('RR+', trp)})
cr = cl.mem('C', 'RR'); tr = cl.mem('T', 'RR'); ncr = cl.mem('-u C', 'RR'); ntr = cl.mem('-u T', 'RR')
cc = w.s([cr], 'recnd', '( %s -> C e. CC )' % A0); tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
ncc = w.s([cc], 'negcld', '( %s -> -u C e. CC )' % A0); ntc = w.s([tc], 'negcld', '( %s -> -u T e. CC )' % A0)
cne = w.s([crp], 'rpne0d', '( %s -> C =/= 0 )' % A0)
ucrp = w.s([urp, cr], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UC)); cl.have(UC, 'RR+', ucrp); cl.atom(UC)
fcn = pkfcn_(w, A0, urp)
lo = cptcl(w, A0, 'C', '-u T', cr, ntr); hi = cptcl(w, A0, 'C', 'T', cr, tr); m1 = cptcl(w, A0, 'C', '-u C', cr, ncr); m2 = cptcl(w, A0, 'C', 'C', cr, cr)
ss = segv(w, A0, 'C', '-u T', 'T', cr, cne, ntr, tr)
ss2 = segv(w, A0, 'C', '-u C', 'T', cr, cne, ncr, tr)
pre1 = w.s([w.s([lo, hi], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, LO, HI)), w.s([fcn, ss], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A0, PK0, DOM, LO, HI, DOM))],
           'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) ) )' % (A0, LO, HI, PK0, DOM, LO, HI, DOM))
pre2 = w.s([w.s([m1, hi], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, M1, HI)), w.s([fcn, ss2], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A0, PK0, DOM, M1, HI, DOM))],
           'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) ) )' % (A0, M1, HI, PK0, DOM, M1, HI, DOM))
# S1 e. [0,1] and the first split point
t2rp = w.s([a1(w, A0, '2rp', '2 e. RR+'), trp], 'rpmulcld', '( %s -> ( 2 x. T ) e. RR+ )' % A0)
tcr = cl.mem('( T - C )', 'RR'); tc0 = linarith(w, A0, [cle], '0 <_ ( T - C )', closure=cl)
s1r = w.s([tcr, t2rp], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, S1))
s10 = w.s([tcr, t2rp, tc0], 'divge0d', '( %s -> 0 <_ %s )' % (A0, S1))
tcle = linarith(w, A0, [cl.gt0('C'), cl.gt0('T')], '( T - C ) <_ ( 2 x. T )', closure=cl)
s11 = w.s([w.s([tcr, cl.mem('( 2 x. T )', 'RR'), t2rp, tcle], 'lediv1dd', '( %s -> %s <_ ( ( 2 x. T ) / ( 2 x. T ) ) )' % (A0, S1)),
           w.s([w.s([t2rp], 'rpcnd', '( %s -> ( 2 x. T ) e. CC )' % A0), w.s([t2rp], 'rpne0d', '( %s -> ( 2 x. T ) =/= 0 )' % A0), w.inst('divid')], 'syl2anc', '( %s -> ( ( 2 x. T ) / ( 2 x. T ) ) = 1 )' % A0)],
          'breqtrd', '( %s -> %s <_ 1 )' % (A0, S1))
s1u = w.s([w.s([s1r, s10, s11], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (A0, S1, S1, S1)),
           w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. %s <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) ) )' % (A0, S1, XC, S1, S1, S1))],
          'mpbird', '( %s -> %s e. %s )' % (A0, S1, XC))
dif1 = vdiff(w, A0, 'C', '-u T', 'T', cc, ntc, tc)
tt = w.s([w.s([tc, tc], 'subnegd', '( %s -> ( T - -u T ) = ( T + T ) )' % A0), w.s([w.s([tc], '2timesd', '( %s -> ( 2 x. T ) = ( T + T ) )' % A0)], 'eqcomd', '( %s -> ( T + T ) = ( 2 x. T ) )' % A0)], 'eqtrd',
         '( %s -> ( T - -u T ) = ( 2 x. T ) )' % A0)
ii = a1(w, A0, 'ax-icn', '_i e. CC')
s1c = w.s([s1r], 'recnd', '( %s -> %s e. CC )' % (A0, S1)); t2c = w.s([t2rp], 'rpcnd', '( %s -> ( 2 x. T ) e. CC )' % A0)
p1 = w.s([w.s([dif1, w.s([tt], 'oveq2d', '( %s -> ( _i x. ( T - -u T ) ) = ( _i x. ( 2 x. T ) ) )' % A0)], 'eqtrd', '( %s -> ( %s - %s ) = ( _i x. ( 2 x. T ) ) )' % (A0, HI, LO))], 'oveq2d',
          '( %s -> ( %s x. ( %s - %s ) ) = ( %s x. ( _i x. ( 2 x. T ) ) ) )' % (A0, S1, HI, LO, S1))
p2 = w.s([s1c, ii, t2c], 'mul12d', '( %s -> ( %s x. ( _i x. ( 2 x. T ) ) ) = ( _i x. ( %s x. ( 2 x. T ) ) ) )' % (A0, S1, S1))
p3 = w.s([w.s([w.s([tcr], 'recnd', '( %s -> ( T - C ) e. CC )' % A0), t2c, w.s([t2rp], 'rpne0d', '( %s -> ( 2 x. T ) =/= 0 )' % A0)], 'divcan1d', '( %s -> ( %s x. ( 2 x. T ) ) = ( T - C ) )' % (A0, S1))], 'oveq2d',
          '( %s -> ( _i x. ( %s x. ( 2 x. T ) ) ) = ( _i x. ( T - C ) ) )' % (A0, S1))
p4 = w.s([w.s([p1, p2], 'eqtrd', '( %s -> ( %s x. ( %s - %s ) ) = ( _i x. ( %s x. ( 2 x. T ) ) ) )' % (A0, S1, HI, LO, S1)), p3], 'eqtrd', '( %s -> ( %s x. ( %s - %s ) ) = ( _i x. ( T - C ) ) )' % (A0, S1, HI, LO))
int_ = w.s([ii, ntc], 'mulcld', '( %s -> ( _i x. -u T ) e. CC )' % A0); itc = w.s([ii, w.s([tcr], 'recnd', '( %s -> ( T - C ) e. CC )' % A0)], 'mulcld', '( %s -> ( _i x. ( T - C ) ) e. CC )' % A0)
p5 = w.s([cc, int_, itc], 'addassd', '( %s -> ( ( C + ( _i x. -u T ) ) + ( _i x. ( T - C ) ) ) = ( C + ( ( _i x. -u T ) + ( _i x. ( T - C ) ) ) ) )' % A0)
p6 = w.s([w.s([ii, ntc, w.s([tcr], 'recnd', '( %s -> ( T - C ) e. CC )' % A0)], 'adddid', '( %s -> ( _i x. ( -u T + ( T - C ) ) ) = ( ( _i x. -u T ) + ( _i x. ( T - C ) ) ) )' % A0)], 'eqcomd',
          '( %s -> ( ( _i x. -u T ) + ( _i x. ( T - C ) ) ) = ( _i x. ( -u T + ( T - C ) ) ) )' % A0)
p7 = w.s([lineq(w, A0, '( -u T + ( T - C ) )', '-u C', closure=cl)], 'oveq2d', '( %s -> ( _i x. ( -u T + ( T - C ) ) ) = ( _i x. -u C ) )' % A0)
m1eq = w.s([w.s([w.s([p4], 'oveq2d', '( %s -> ( %s + ( %s x. ( %s - %s ) ) ) = ( %s + ( _i x. ( T - C ) ) ) )' % (A0, LO, S1, HI, LO, LO)), p5], 'eqtrd',
                '( %s -> ( %s + ( %s x. ( %s - %s ) ) ) = ( C + ( ( _i x. -u T ) + ( _i x. ( T - C ) ) ) ) )' % (A0, LO, S1, HI, LO)),
           w.s([w.s([p6, p7], 'eqtrd', '( %s -> ( ( _i x. -u T ) + ( _i x. ( T - C ) ) ) = ( _i x. -u C ) )' % A0)], 'oveq2d', '( %s -> ( C + ( ( _i x. -u T ) + ( _i x. ( T - C ) ) ) ) = %s )' % (A0, M1))], 'eqtrd',
           '( %s -> ( %s + ( %s x. ( %s - %s ) ) ) = %s )' % (A0, LO, S1, HI, LO, M1))
sp1 = w.s([pre1, s1u, w.s([m1eq], 'eqcomd', '( %s -> %s = ( %s + ( %s x. ( %s - %s ) ) ) )' % (A0, M1, LO, S1, HI, LO)), w.inst('lintsplit')], 'syl3anc',
          '( %s -> %s = ( %s + %s ) )' % (A0, PK, E(LO, M1), E(M1, HI)))
# S2 and the second split point
tcrp = w.s([trp, crp], 'rpaddcld', '( %s -> ( T + C ) e. RR+ )' % A0)
c2r = cl.mem('( 2 x. C )', 'RR'); c20 = linarith(w, A0, [cl.gt0('C')], '0 <_ ( 2 x. C )', closure=cl)
s2r = w.s([c2r, tcrp], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, S2))
s20 = w.s([c2r, tcrp, c20], 'divge0d', '( %s -> 0 <_ %s )' % (A0, S2))
c2le = linarith(w, A0, [cle], '( 2 x. C ) <_ ( T + C )', closure=cl)
s21 = w.s([w.s([c2r, cl.mem('( T + C )', 'RR'), tcrp, c2le], 'lediv1dd', '( %s -> %s <_ ( ( T + C ) / ( T + C ) ) )' % (A0, S2)),
           w.s([w.s([tcrp], 'rpcnd', '( %s -> ( T + C ) e. CC )' % A0), w.s([tcrp], 'rpne0d', '( %s -> ( T + C ) =/= 0 )' % A0), w.inst('divid')], 'syl2anc', '( %s -> ( ( T + C ) / ( T + C ) ) = 1 )' % A0)],
          'breqtrd', '( %s -> %s <_ 1 )' % (A0, S2))
s2u = w.s([w.s([s2r, s20, s21], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (A0, S2, S2, S2)),
           w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. %s <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) ) )' % (A0, S2, XC, S2, S2, S2))],
          'mpbird', '( %s -> %s e. %s )' % (A0, S2, XC))
dif2 = vdiff(w, A0, 'C', '-u C', 'T', cc, ncc, tc)
tpc = w.s([tc, cc], 'subnegd', '( %s -> ( T - -u C ) = ( T + C ) )' % A0)
s2c = w.s([s2r], 'recnd', '( %s -> %s e. CC )' % (A0, S2)); tpcc = w.s([tcrp], 'rpcnd', '( %s -> ( T + C ) e. CC )' % A0)
q1 = w.s([w.s([dif2, w.s([tpc], 'oveq2d', '( %s -> ( _i x. ( T - -u C ) ) = ( _i x. ( T + C ) ) )' % A0)], 'eqtrd', '( %s -> ( %s - %s ) = ( _i x. ( T + C ) ) )' % (A0, HI, M1))], 'oveq2d',
          '( %s -> ( %s x. ( %s - %s ) ) = ( %s x. ( _i x. ( T + C ) ) ) )' % (A0, S2, HI, M1, S2))
q2 = w.s([s2c, ii, tpcc], 'mul12d', '( %s -> ( %s x. ( _i x. ( T + C ) ) ) = ( _i x. ( %s x. ( T + C ) ) ) )' % (A0, S2, S2))
q3 = w.s([w.s([w.s([c2r], 'recnd', '( %s -> ( 2 x. C ) e. CC )' % A0), tpcc, w.s([tcrp], 'rpne0d', '( %s -> ( T + C ) =/= 0 )' % A0)], 'divcan1d', '( %s -> ( %s x. ( T + C ) ) = ( 2 x. C ) )' % (A0, S2))], 'oveq2d',
          '( %s -> ( _i x. ( %s x. ( T + C ) ) ) = ( _i x. ( 2 x. C ) ) )' % (A0, S2))
q4 = w.s([w.s([q1, q2], 'eqtrd', '( %s -> ( %s x. ( %s - %s ) ) = ( _i x. ( %s x. ( T + C ) ) ) )' % (A0, S2, HI, M1, S2)), q3], 'eqtrd', '( %s -> ( %s x. ( %s - %s ) ) = ( _i x. ( 2 x. C ) ) )' % (A0, S2, HI, M1))
inc = w.s([ii, ncc], 'mulcld', '( %s -> ( _i x. -u C ) e. CC )' % A0); i2c = w.s([ii, w.s([c2r], 'recnd', '( %s -> ( 2 x. C ) e. CC )' % A0)], 'mulcld', '( %s -> ( _i x. ( 2 x. C ) ) e. CC )' % A0)
q5 = w.s([cc, inc, i2c], 'addassd', '( %s -> ( ( C + ( _i x. -u C ) ) + ( _i x. ( 2 x. C ) ) ) = ( C + ( ( _i x. -u C ) + ( _i x. ( 2 x. C ) ) ) ) )' % A0)
q6 = w.s([w.s([ii, ncc, w.s([c2r], 'recnd', '( %s -> ( 2 x. C ) e. CC )' % A0)], 'adddid', '( %s -> ( _i x. ( -u C + ( 2 x. C ) ) ) = ( ( _i x. -u C ) + ( _i x. ( 2 x. C ) ) ) )' % A0)], 'eqcomd',
          '( %s -> ( ( _i x. -u C ) + ( _i x. ( 2 x. C ) ) ) = ( _i x. ( -u C + ( 2 x. C ) ) ) )' % A0)
q7 = w.s([lineq(w, A0, '( -u C + ( 2 x. C ) )', 'C', closure=cl)], 'oveq2d', '( %s -> ( _i x. ( -u C + ( 2 x. C ) ) ) = ( _i x. C ) )' % A0)
m2eq = w.s([w.s([w.s([q4], 'oveq2d', '( %s -> ( %s + ( %s x. ( %s - %s ) ) ) = ( %s + ( _i x. ( 2 x. C ) ) ) )' % (A0, M1, S2, HI, M1, M1)), q5], 'eqtrd',
                '( %s -> ( %s + ( %s x. ( %s - %s ) ) ) = ( C + ( ( _i x. -u C ) + ( _i x. ( 2 x. C ) ) ) ) )' % (A0, M1, S2, HI, M1)),
           w.s([w.s([q6, q7], 'eqtrd', '( %s -> ( ( _i x. -u C ) + ( _i x. ( 2 x. C ) ) ) = ( _i x. C ) )' % A0)], 'oveq2d', '( %s -> ( C + ( ( _i x. -u C ) + ( _i x. ( 2 x. C ) ) ) ) = %s )' % (A0, M2))], 'eqtrd',
           '( %s -> ( %s + ( %s x. ( %s - %s ) ) ) = %s )' % (A0, M1, S2, HI, M1, M2))
sp2 = w.s([pre2, s2u, w.s([m2eq], 'eqcomd', '( %s -> %s = ( %s + ( %s x. ( %s - %s ) ) ) )' % (A0, M2, M1, S2, HI, M1)), w.inst('lintsplit')], 'syl3anc',
          '( %s -> %s = ( %s + %s ) )' % (A0, E(M1, HI), E(M1, M2), E(M2, HI)))
# closures and the triangle inequalities
e1c, _ = edgecl(w, A0, LO, M1, lo, m1, fcn, segv(w, A0, 'C', '-u T', '-u C', cr, cne, ntr, ncr))
e2c, _ = edgecl(w, A0, M1, M2, m1, m2, fcn, segv(w, A0, 'C', '-u C', 'C', cr, cne, ncr, cr))
e3c, _ = edgecl(w, A0, M2, HI, m2, hi, fcn, segv(w, A0, 'C', 'C', 'T', cr, cne, cr, tr))
e23c = w.s([e2c, e3c], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, E(M1, M2), E(M2, HI)))
tri1 = w.s([e1c, e23c], 'abstrid', '( %s -> ( abs ` ( %s + ( %s + %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( %s + %s ) ) ) )' % (A0, E(LO, M1), E(M1, M2), E(M2, HI), E(LO, M1), E(M1, M2), E(M2, HI)))
tri2 = w.s([e2c, e3c], 'abstrid', '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, E(M1, M2), E(M2, HI), E(M1, M2), E(M2, HI)))
pkeq = w.s([sp1, w.s([sp2], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + ( %s + %s ) ) )' % (A0, E(LO, M1), E(M1, HI), E(LO, M1), E(M1, M2), E(M2, HI)))], 'eqtrd',
           '( %s -> %s = ( %s + ( %s + %s ) ) )' % (A0, PK, E(LO, M1), E(M1, M2), E(M2, HI)))
abspk = w.s([w.s([pkeq], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( %s + ( %s + %s ) ) ) )' % (A0, PK, E(LO, M1), E(M1, M2), E(M2, HI))), tri1], 'eqbrtrd',
            '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s + %s ) ) ) )' % (A0, PK, E(LO, M1), E(M1, M2), E(M2, HI)))
# the three bounds
b1 = w.s([w.s([w.s([urp, crp], 'jca', '( %s -> ( U e. RR+ /\\ C e. RR+ ) )' % A0), w.s([w.s([trp, crp], 'jca', '( %s -> ( T e. RR+ /\\ C e. RR+ ) )' % A0), cle], 'jca', '( %s -> ( ( T e. RR+ /\\ C e. RR+ ) /\\ C <_ T ) )' % A0)], 'jca',
               '( %s -> ( ( U e. RR+ /\\ C e. RR+ ) /\\ ( ( T e. RR+ /\\ C e. RR+ ) /\\ C <_ T ) ) )' % A0), w.inst('pkvlogn')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, E(LO, M1), UC, D))
b3 = w.s([w.s([w.s([urp, crp], 'jca', '( %s -> ( U e. RR+ /\\ C e. RR+ ) )' % A0), w.s([w.s([crp, trp], 'jca', '( %s -> ( C e. RR+ /\\ T e. RR+ ) )' % A0), cle], 'jca', '( %s -> ( ( C e. RR+ /\\ T e. RR+ ) /\\ C <_ T ) )' % A0)], 'jca',
               '( %s -> ( ( U e. RR+ /\\ C e. RR+ ) /\\ ( ( C e. RR+ /\\ T e. RR+ ) /\\ C <_ T ) ) )' % A0), w.inst('pkvlog')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, E(M2, HI), UC, D))
vb = w.s([w.s([w.s([urp, w.s([cr, cne], 'jca', '( %s -> ( C e. RR /\\ C =/= 0 ) )' % A0)], 'jca', '( %s -> ( U e. RR+ /\\ ( C e. RR /\\ C =/= 0 ) ) )' % A0), w.s([ncr, cr], 'jca', '( %s -> ( -u C e. RR /\\ C e. RR ) )' % A0)], 'jca',
              '( %s -> ( ( U e. RR+ /\\ ( C e. RR /\\ C =/= 0 ) ) /\\ ( -u C e. RR /\\ C e. RR ) ) )' % A0), w.inst('vedgbnd')], 'syl',
         '( %s -> ( abs ` %s ) <_ ( ( %s / ( abs ` C ) ) x. ( abs ` ( %s - %s ) ) ) )' % (A0, E(M1, M2), UC, M2, M1))
absc = w.s([cr, w.s([crp], 'rpge0d', '( %s -> 0 <_ C )' % A0)], 'absidd', '( %s -> ( abs ` C ) = C )' % A0)
dif3 = vdiff(w, A0, 'C', '-u C', 'C', cc, ncc, cc)
cc2 = w.s([w.s([cc, cc], 'subnegd', '( %s -> ( C - -u C ) = ( C + C ) )' % A0), w.s([w.s([cc], '2timesd', '( %s -> ( 2 x. C ) = ( C + C ) )' % A0)], 'eqcomd', '( %s -> ( C + C ) = ( 2 x. C ) )' % A0)], 'eqtrd',
          '( %s -> ( C - -u C ) = ( 2 x. C ) )' % A0)
c2rp = w.s([a1(w, A0, '2rp', '2 e. RR+'), crp], 'rpmulcld', '( %s -> ( 2 x. C ) e. RR+ )' % A0)
absd = w.s([w.s([w.s([dif3], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( C - -u C ) ) ) )' % (A0, M2, M1)), absi_(w, A0, '( C - -u C )', w.s([cc, ncc], 'subcld', '( %s -> ( C - -u C ) e. CC )' % A0))], 'eqtrd',
                '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( C - -u C ) ) )' % (A0, M2, M1)),
           w.s([w.s([cc2], 'fveq2d', '( %s -> ( abs ` ( C - -u C ) ) = ( abs ` ( 2 x. C ) ) )' % A0), w.s([w.s([c2rp], 'rpred', '( %s -> ( 2 x. C ) e. RR )' % A0), w.s([c2rp], 'rpge0d', '( %s -> 0 <_ ( 2 x. C ) )' % A0)], 'absidd', '( %s -> ( abs ` ( 2 x. C ) ) = ( 2 x. C ) )' % A0)],
               'eqtrd', '( %s -> ( abs ` ( C - -u C ) ) = ( 2 x. C ) )' % A0)], 'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = ( 2 x. C ) )' % (A0, M2, M1))
ucc = w.s([ucrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC))
vbv = w.s([w.s([w.s([absc], 'oveq2d', '( %s -> ( %s / ( abs ` C ) ) = ( %s / C ) )' % (A0, UC, UC)), absd], 'oveq12d', '( %s -> ( ( %s / ( abs ` C ) ) x. ( abs ` ( %s - %s ) ) ) = ( ( %s / C ) x. ( 2 x. C ) ) )' % (A0, UC, M2, M1, UC)),
           w.s([w.s([w.s([ucc, cc, cne], 'divcld', '( %s -> ( %s / C ) e. CC )' % (A0, UC)), w.s([c2rp], 'rpcnd', '( %s -> ( 2 x. C ) e. CC )' % A0)], 'mulcomd', '( %s -> ( ( %s / C ) x. ( 2 x. C ) ) = ( ( 2 x. C ) x. ( %s / C ) ) )' % (A0, UC, UC)),
                w.s([w.s([a1(w, A0, '2cn', '2 e. CC'), cc, w.s([ucc, cc, cne], 'divcld', '( %s -> ( %s / C ) e. CC )' % (A0, UC))], 'mulassd', '( %s -> ( ( 2 x. C ) x. ( %s / C ) ) = ( 2 x. ( C x. ( %s / C ) ) ) )' % (A0, UC, UC)),
                     w.s([w.s([ucc, cc, cne], 'divcan2d', '( %s -> ( C x. ( %s / C ) ) = %s )' % (A0, UC, UC))], 'oveq2d', '( %s -> ( 2 x. ( C x. ( %s / C ) ) ) = ( 2 x. %s ) )' % (A0, UC, UC))], 'eqtrd',
                    '( %s -> ( ( 2 x. C ) x. ( %s / C ) ) = ( 2 x. %s ) )' % (A0, UC, UC))], 'eqtrd', '( %s -> ( ( %s / C ) x. ( 2 x. C ) ) = ( 2 x. %s ) )' % (A0, UC, UC))], 'eqtrd',
          '( %s -> ( ( %s / ( abs ` C ) ) x. ( abs ` ( %s - %s ) ) ) = ( 2 x. %s ) )' % (A0, UC, M2, M1, UC))
b2 = w.s([vb, vbv], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( 2 x. %s ) )' % (A0, E(M1, M2), UC))
# the sum
lt_ = w.s([trp, w.inst('relogcl')], 'syl', '( %s -> ( log ` T ) e. RR )' % A0); lc_ = w.s([crp, w.inst('relogcl')], 'syl', '( %s -> ( log ` C ) e. RR )' % A0)
cl.have('( log ` T )', 'RR', lt_); cl.have('( log ` C )', 'RR', lc_); cl.atom('( log ` T )'); cl.atom('( log ` C )')
for X_, st in ((E(LO, M1), e1c), (E(M1, M2), e2c), (E(M2, HI), e3c), (PK, w.s([urp, crp, trp, w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (A0, PK)))):
    cl.atom('( abs ` %s )' % X_); cl.have('( abs ` %s )' % X_, 'RR', w.s([st], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, X_)))
cl.atom('( abs ` ( %s + %s ) )' % (E(M1, M2), E(M2, HI))); cl.have('( abs ` ( %s + %s ) )' % (E(M1, M2), E(M2, HI)), 'RR', w.s([e23c], 'abscld', '( %s -> ( abs ` ( %s + %s ) ) e. RR )' % (A0, E(M1, M2), E(M2, HI))))
fin = linarith(w, A0, [abspk, tri2, b1, b2, b3], '( abs ` %s ) <_ ( ( 2 x. %s ) x. ( 1 + %s ) )' % (PK, UC, D), closure=cl, products=True)
rld = w.s([w.s([trp, crp, w.inst('relogdiv')], 'syl2anc', '( %s -> ( log ` ( T / C ) ) = %s )' % (A0, D))], 'eqcomd', '( %s -> %s = ( log ` ( T / C ) ) )' % (A0, D))
w.qed([fin, w.s([w.s([rld], 'oveq2d', '( %s -> ( 1 + %s ) = ( 1 + ( log ` ( T / C ) ) ) )' % (A0, D))], 'oveq2d', '( %s -> ( ( 2 x. %s ) x. ( 1 + %s ) ) = ( ( 2 x. %s ) x. ( 1 + ( log ` ( T / C ) ) ) ) )' % (A0, UC, D, UC))],
      'breqtrd', '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. ( 1 + ( log ` ( T / C ) ) ) ) )' % (A0, PK, UC))
run7(w)
