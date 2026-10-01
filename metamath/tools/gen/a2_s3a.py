"""Sortie A2, batch 8: the scale facts of Step3W (the reservoir subset Q, the
logarithms of z and x = L ^ 5)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

FP = '( ~P Prime i^i Fin )'
A2 = '( ell2 ` N )'; A3 = '( ell3 ` N )'
ZR = '( ( C x. %s ) x. %s )' % (A2, A3)
GPW = '( ( Z goodPrimesW W ) ` Y )'
TY = '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'

# ------------------------------------------------------------------- s3sfp
w = W('s3sfp', 'A subset of the windowed reservoir is a finite set of primes.')
A = '( %s /\\ S C_ %s )' % (TY, GPW)
ty = w.s([], 'simpl', '( %s -> %s )' % (A, TY))
ss = w.s([], 'simpr', '( %s -> S C_ %s )' % (A, GPW))
gf = w.s([ty, w.inst('goodprimeswfi')], 'syl', '( %s -> %s e. %s )' % (A, GPW, FP))
gb = w.s([gf, w.inst('elfpw')], 'sylib', '( %s -> ( %s C_ Prime /\\ %s e. Fin ) )' % (A, GPW, GPW))
gs = w.s([gb], 'simpld', '( %s -> %s C_ Prime )' % (A, GPW))
gfi = w.s([gb], 'simprd', '( %s -> %s e. Fin )' % (A, GPW))
sp = w.s([ss, gs], 'sstrd', '( %s -> S C_ Prime )' % A)
sfi = w.s([gfi, ss, w.inst('ssfi')], 'syl2anc', '( %s -> S e. Fin )' % A)
w.qed([w.s([sp, sfi], 'jca', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % A), w.inst('elfpw')], 'sylibr',
      '( %s -> S e. %s )' % (A, FP))
run(w)

# ------------------------------------------------------------------ s3sbnd
w = W('s3sbnd', 'An element of the windowed reservoir is a prime in ( w , z ] .')
A = '( %s /\\ S C_ %s /\\ P e. S )' % (TY, GPW)
ty = w.s([], 'simp1', '( %s -> %s )' % (A, TY))
ss = w.s([], 'simp2', '( %s -> S C_ %s )' % (A, GPW))
pin = w.s([], 'simp3', '( %s -> P e. S )' % A)
pg = w.s([ss, pin], 'sseldd', '( %s -> P e. %s )' % (A, GPW))
bi = w.s([ty, w.inst('elgoodprimesw')], 'syl',
         '( %s -> ( P e. %s <-> ( P e. ( 0 ... Z ) /\\ ( P e. Prime /\\ W < P /\\ A. p e. Prime ( p || ( P - 1 ) -> p <_ Y ) ) ) ) )' % (A, GPW))
b = w.s([pg, bi], 'mpbid', '( %s -> ( P e. ( 0 ... Z ) /\\ ( P e. Prime /\\ W < P /\\ A. p e. Prime ( p || ( P - 1 ) -> p <_ Y ) ) ) )' % A)
pfz = w.s([b], 'simpld', '( %s -> P e. ( 0 ... Z ) )' % A)
pr = w.s([b], 'simprd', '( %s -> ( P e. Prime /\\ W < P /\\ A. p e. Prime ( p || ( P - 1 ) -> p <_ Y ) ) )' % A)
ple = w.s([pfz, w.inst('elfzle2')], 'syl', '( %s -> P <_ Z )' % A)
wlt = w.s([pr], 'simp2d', '( %s -> W < P )' % A)
w.qed([ple, wlt], 'jca', '( %s -> ( P <_ Z /\\ W < P ) )' % A)
run(w)

# --------------------------------------------------- s3logzlb, s3logzub
def zctx(w):
    d = {}
    d['cr'] = w.h('C e. RR')
    d['c1000'] = w.h('; ; ; 1 0 0 0 <_ C')
    d['n3'] = w.h('N e. ( ZZ>= ` 3 )')
    d['a50'] = w.h('; 5 0 <_ %s' % A2)
    d['b200'] = w.h('; ; 2 0 0 <_ %s' % A3)
    d['zn0'] = w.h('Z e. NN0')
    d['zlo'] = w.h('%s <_ Z' % ZR)
    return d


def zbasics(w, d, A='ph'):
    d['n2'] = w.s([d['n3'], w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
    d['n0'] = w.s([w.s([d['n2'], w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % A)], 'nnnn0d', '( %s -> N e. NN0 )' % A)
    d['ar'] = w.s([d['n2'], w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, A2))
    d['br'] = w.s([d['n3'], w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, A3))
    LV = {'C': d['cr'], A2: d['ar'], A3: d['br']}
    d['LV'] = LV
    d['c1'] = linarith(w, A, [d['c1000']], '1 <_ C', leaves=LV)
    d['c0'] = linarith(w, A, [d['c1000']], '0 < C', leaves=LV)
    d['a0'] = linarith(w, A, [d['a50']], '0 < %s' % A2, leaves=LV)
    d['a1'] = linarith(w, A, [d['a50']], '1 <_ %s' % A2, leaves=LV)
    d['ag0'] = w.s([d['a0']], 'ltled', '( %s -> 0 <_ %s )' % (A, A2))
    d['b0'] = linarith(w, A, [d['b200']], '0 < %s' % A3, leaves=LV)
    d['b1'] = linarith(w, A, [d['b200']], '1 <_ %s' % A3, leaves=LV)
    d['bg0'] = w.s([d['b0']], 'ltled', '( %s -> 0 <_ %s )' % (A, A3))
    d['arp'] = w.s([d['ar'], d['a0']], 'elrpd', '( %s -> %s e. RR+ )' % (A, A2))
    d['brp'] = w.s([d['br'], d['b0']], 'elrpd', '( %s -> %s e. RR+ )' % (A, A3))
    d['crp'] = w.s([d['cr'], d['c0']], 'elrpd', '( %s -> C e. RR+ )' % A)
    d['zr'] = w.s([d['zn0']], 'nn0red', '( %s -> Z e. RR )' % A)
    d['zrr'] = w.s([w.s([d['cr'], d['ar']], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (A, A2)), d['br']], 'remulcld',
                   '( %s -> %s e. RR )' % (A, ZR))
    d['cb'] = w.s([d['cr'], d['br']], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (A, A3))
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    cb1 = w.s([one, d['cr'], one, d['br'],
               w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A),
               w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A),
               d['c1'], d['b1']], 'lemul12ad', '( %s -> ( 1 x. 1 ) <_ ( C x. %s ) )' % (A, A3))
    t11 = w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % A)
    d['cb1'] = w.s([w.s([t11], 'eqcomd', '( %s -> 1 = ( 1 x. 1 ) )' % A), cb1], 'eqbrtrd', '( %s -> 1 <_ ( C x. %s ) )' % (A, A3))
    # a <_ ( C x. a ) x. b
    ac = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A, A2))
    bc = w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A, A3))
    cc_ = w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A)
    e1 = w.s([cc_, ac, bc], 'mul32d', '( %s -> %s = ( ( C x. %s ) x. %s ) )' % (A, ZR, A3, A2))
    e2 = w.s([w.s([cc_, bc], 'mulcld', '( %s -> ( C x. %s ) e. CC )' % (A, A3)), ac], 'mulcomd',
             '( %s -> ( ( C x. %s ) x. %s ) = ( %s x. ( C x. %s ) ) )' % (A, A3, A2, A2, A3))
    d['rot'] = w.s([e1, e2], 'eqtrd', '( %s -> %s = ( %s x. ( C x. %s ) ) )' % (A, ZR, A2, A3))
    mg = w.s([one, d['cb'], d['ar'], d['ag0'], d['cb1']], 'lemul2ad', '( %s -> ( %s x. 1 ) <_ ( %s x. ( C x. %s ) ) )' % (A, A2, A2, A3))
    mg2 = w.s([w.s([w.s([ac], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A, A2, A2))], 'eqcomd',
                   '( %s -> %s = ( %s x. 1 ) )' % (A, A2, A2)), mg], 'eqbrtrd', '( %s -> %s <_ ( %s x. ( C x. %s ) ) )' % (A, A2, A2, A3))
    d['alez'] = w.s([d['ar'], d['zrr'], d['zr'], w.s([mg2, w.s([d['rot']], 'eqcomd', '( %s -> ( %s x. ( C x. %s ) ) = %s )' % (A, A2, A3, ZR))], 'breqtrd',
                                                     '( %s -> %s <_ %s )' % (A, A2, ZR)), d['zlo']], 'letrd', '( %s -> %s <_ Z )' % (A, A2))
    d['z0'] = linarith(w, A, [d['alez'], d['a50']], '0 < Z', leaves={A2: d['ar'], 'Z': d['zr']})
    d['zrp'] = w.s([d['zr'], d['z0']], 'elrpd', '( %s -> Z e. RR+ )' % A)
    d['lzr'] = w.s([d['zrp'], w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
    return d


w = WH('s3logzlb', 'ell3 n <_ log z at windowed scales (Lean: Step3W.lean hlogz_lb).')
d = zctx(w)
zbasics(w, d)
A = 'ph'
bi = w.s([d['arp'], d['zrp'], w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ Z <-> ( log ` %s ) <_ ( log ` Z ) ) )' % (A, A2, A2))
ll = w.s([d['alez'], bi], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` Z ) )' % (A, A2))
iv = w.s([d['n0'], w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, A3, A2))
w.qed([iv, ll], 'eqbrtrd', '( %s -> %s <_ ( log ` Z ) )' % (A, A3))
run(w)

w = WH('s3logzub', 'log z <_ 3 ell3 n at windowed scales (Lean: Step3W.lean hlogz_ub).')
d = zctx(w)
lg4c = w.h('( log ` ( 4 x. C ) ) <_ %s' % A3)
zhi = w.h('Z <_ ( 4 x. %s )' % ZR)
zbasics(w, d)
A = 'ph'
ac = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A, A2))
bc = w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A, A3))
cc_ = w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A)
c4 = w.s([w.s([], '4cn', '4 e. CC')], 'a1i', '( %s -> 4 e. CC )' % A)
e1 = w.s([cc_, ac, bc], 'mulassd', '( %s -> ( ( C x. %s ) x. %s ) = ( C x. ( %s x. %s ) ) )' % (A, A2, A3, A2, A3))
e2 = w.s([e1], 'oveq2d', '( %s -> ( 4 x. %s ) = ( 4 x. ( C x. ( %s x. %s ) ) ) )' % (A, ZR, A2, A3))
e3 = w.s([c4, cc_, w.s([ac, bc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A, A2, A3))], 'mulassd',
         '( %s -> ( ( 4 x. C ) x. ( %s x. %s ) ) = ( 4 x. ( C x. ( %s x. %s ) ) ) )' % (A, A2, A3, A2, A3))
eq = w.s([e2, w.s([e3], 'eqcomd', '( %s -> ( 4 x. ( C x. ( %s x. %s ) ) ) = ( ( 4 x. C ) x. ( %s x. %s ) ) )' % (A, A2, A3, A2, A3))], 'eqtrd',
         '( %s -> ( 4 x. %s ) = ( ( 4 x. C ) x. ( %s x. %s ) ) )' % (A, ZR, A2, A3))
zle = w.s([zhi, eq], 'breqtrd', '( %s -> Z <_ ( ( 4 x. C ) x. ( %s x. %s ) ) )' % (A, A2, A3))
r4 = w.s([w.s([], '4rp', '4 e. RR+')], 'a1i', '( %s -> 4 e. RR+ )' % A)
c4rp = w.s([r4, d['crp']], 'rpmulcld', '( %s -> ( 4 x. C ) e. RR+ )' % A)
abrp = w.s([d['arp'], d['brp']], 'rpmulcld', '( %s -> ( %s x. %s ) e. RR+ )' % (A, A2, A3))
prp = w.s([c4rp, abrp], 'rpmulcld', '( %s -> ( ( 4 x. C ) x. ( %s x. %s ) ) e. RR+ )' % (A, A2, A3))
bi = w.s([d['zrp'], prp, w.inst('logleb')], 'syl2anc',
         '( %s -> ( Z <_ ( ( 4 x. C ) x. ( %s x. %s ) ) <-> ( log ` Z ) <_ ( log ` ( ( 4 x. C ) x. ( %s x. %s ) ) ) ) )' % (A, A2, A3, A2, A3))
ll = w.s([zle, bi], 'mpbid', '( %s -> ( log ` Z ) <_ ( log ` ( ( 4 x. C ) x. ( %s x. %s ) ) ) )' % (A, A2, A3))
lm1 = w.s([c4rp, abrp, w.inst('relogmul')], 'syl2anc',
          '( %s -> ( log ` ( ( 4 x. C ) x. ( %s x. %s ) ) ) = ( ( log ` ( 4 x. C ) ) + ( log ` ( %s x. %s ) ) ) )' % (A, A2, A3, A2, A3))
lm2 = w.s([d['arp'], d['brp'], w.inst('relogmul')], 'syl2anc',
          '( %s -> ( log ` ( %s x. %s ) ) = ( ( log ` %s ) + ( log ` %s ) ) )' % (A, A2, A3, A2, A3))
iv = w.s([d['n0'], w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, A3, A2))
lm3 = w.s([lm2, w.s([w.s([iv], 'eqcomd', '( %s -> ( log ` %s ) = %s )' % (A, A2, A3))], 'oveq1d',
                    '( %s -> ( ( log ` %s ) + ( log ` %s ) ) = ( %s + ( log ` %s ) ) )' % (A, A2, A3, A3, A3))], 'eqtrd',
          '( %s -> ( log ` ( %s x. %s ) ) = ( %s + ( log ` %s ) ) )' % (A, A2, A3, A3, A3))
lm4 = w.s([lm1, w.s([lm3], 'oveq2d', '( %s -> ( ( log ` ( 4 x. C ) ) + ( log ` ( %s x. %s ) ) ) = ( ( log ` ( 4 x. C ) ) + ( %s + ( log ` %s ) ) ) )' % (A, A2, A3, A3, A3))], 'eqtrd',
          '( %s -> ( log ` ( ( 4 x. C ) x. ( %s x. %s ) ) ) = ( ( log ` ( 4 x. C ) ) + ( %s + ( log ` %s ) ) ) )' % (A, A2, A3, A3, A3))
ll2 = w.s([ll, lm4], 'breqtrd', '( %s -> ( log ` Z ) <_ ( ( log ` ( 4 x. C ) ) + ( %s + ( log ` %s ) ) ) )' % (A, A3, A3))
lbb = w.s([w.s([d['br'], d['b1']], 'jca', '( %s -> ( %s e. RR /\\ 1 <_ %s ) )' % (A, A3, A3)), w.inst('loglet')], 'syl',
          '( %s -> ( log ` %s ) <_ %s )' % (A, A3, A3))
l4cr = w.s([c4rp, w.inst('relogcl')], 'syl', '( %s -> ( log ` ( 4 x. C ) ) e. RR )' % A)
lbr = w.s([d['brp'], w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (A, A3))
linarith(w, A, [ll2, lbb, lg4c], '( log ` Z ) <_ ( 3 x. %s )' % A3,
         leaves={'( log ` Z )': d['lzr'], A3: d['br'], '( log ` ( 4 x. C ) )': l4cr, '( log ` %s )' % A3: lbr}, name='qed')
run(w)

# ----------------------------------------------------------- s3sall, s3sallz
w = W('s3sall', 'Every element of a subset of the windowed reservoir lies in ( w , z ] .')
A = '( %s /\\ S C_ %s )' % (TY, GPW)
B = '( %s /\\ r e. S )' % A
ty = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, TY))], 'adantr', '( %s -> %s )' % (B, TY))
ss = w.s([w.s([], 'simpr', '( %s -> S C_ %s )' % (A, GPW))], 'adantr', '( %s -> S C_ %s )' % (B, GPW))
rin = w.s([], 'simpr', '( %s -> r e. S )' % B)
bn = w.s([w.s([ty, ss, rin], '3jca', '( %s -> ( %s /\\ S C_ %s /\\ r e. S ) )' % (B, TY, GPW)), w.inst('s3sbnd')], 'syl',
         '( %s -> ( r <_ Z /\\ W < r ) )' % B)
w.qed([bn], 'ralrimiva', '( %s -> A. r e. S ( r <_ Z /\\ W < r ) )' % A)
run(w)

w = W('s3sallz', 'Every element of a subset of the windowed reservoir is at most z.')
A = '( %s /\\ S C_ %s )' % (TY, GPW)
al = w.s([], 's3sall', '( %s -> A. r e. S ( r <_ Z /\\ W < r ) )' % A)
ri = w.s([w.s([], 'simpl', '( ( r <_ Z /\\ W < r ) -> r <_ Z )')], 'ralimi',
         '( A. r e. S ( r <_ Z /\\ W < r ) -> A. r e. S r <_ Z )')
cb = w.s([w.s([], 'breq1', '( r = p -> ( r <_ Z <-> p <_ Z ) )')], 'cbvralvw', '( A. r e. S r <_ Z <-> A. p e. S p <_ Z )')
st = w.s([al, w.s([ri], 'a1i', '( %s -> ( A. r e. S ( r <_ Z /\\ W < r ) -> A. r e. S r <_ Z ) )' % A)], 'mpd',
         '( %s -> A. r e. S r <_ Z )' % A)
w.qed([st, w.s([cb], 'a1i', '( %s -> ( A. r e. S r <_ Z <-> A. p e. S p <_ Z ) )' % A)], 'mpbid',
      '( %s -> A. p e. S p <_ Z )' % A)
run(w)

# ------------------------------------------------------------------- s3logx
LS = '( Lmod ` S )'; XCS = '( xceil ` S )'
w = WH('s3logx', 'log x <_ 75 ell2 n ell3 n for x = ( Lmod Q ) ^ 5 (Lean: Step3W.lean hlogx_ub).')
n3 = w.h('N e. ( ZZ>= ` 3 )')
a0 = w.h('0 <_ %s' % A2)
b0 = w.h('0 <_ %s' % A3)
zn0 = w.h('Z e. NN0'); wn0 = w.h('W e. NN0'); yn0 = w.h('Y e. NN0')
z0 = w.h('0 < Z')
sub = w.h('S C_ %s' % GPW)
hc = w.h('( # ` S ) = T')
t5 = w.h('T <_ ( 5 x. %s )' % A2)
lz3 = w.h('( log ` Z ) <_ ( 3 x. %s )' % A3)
lz0 = w.h('0 <_ ( log ` Z )')
A = 'ph'
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
ar = w.s([n2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, A2))
br = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, A3))
ty = w.s([zn0, wn0, yn0], '3jca', '( %s -> %s )' % (A, TY))
sfp = w.s([w.s([ty, sub], 'jca', '( %s -> ( %s /\\ S C_ %s ) )' % (A, TY, GPW)), w.inst('s3sfp')], 'syl', '( %s -> S e. %s )' % (A, FP))
sb = w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % A)
sprm = w.s([sb], 'simpld', '( %s -> S C_ Prime )' % A)
sfi = w.s([sb], 'simprd', '( %s -> S e. Fin )' % A)
pn0 = w.s([w.s([], 'prmssnn', 'Prime C_ NN'), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', 'Prime C_ NN0')
sn0 = w.s([sprm, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % A)], 'sstrd', '( %s -> S C_ NN0 )' % A)
sfn0 = w.s([w.s([sn0, sfi], 'jca', '( %s -> ( S C_ NN0 /\\ S e. Fin ) )' % A), w.inst('elfpw')], 'sylibr',
           '( %s -> S e. ( ~P NN0 i^i Fin ) )' % A)
lnn = w.s([sfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (A, LS))
lrp = w.s([lnn], 'nnrpd', '( %s -> %s e. RR+ )' % (A, LS))
hs = w.s([sfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % A)
tn0 = w.s([hc, hs], 'eqeltrrd', '( %s -> T e. NN0 )' % A)
allz = w.s([w.s([ty, sub], 'jca', '( %s -> ( %s /\\ S C_ %s ) )' % (A, TY, GPW)), w.inst('s3sallz')], 'syl',
           '( %s -> A. p e. S p <_ Z )' % A)
ub = w.s([w.s([sfp, zn0, allz], '3jca', '( %s -> ( S e. %s /\\ Z e. NN0 /\\ A. p e. S p <_ Z ) )' % (A, FP)), w.inst('prmprodub')], 'syl',
         '( %s -> %s <_ ( Z ^ ( # ` S ) ) )' % (A, LS))
ub2 = w.s([ub, w.s([hc], 'oveq2d', '( %s -> ( Z ^ ( # ` S ) ) = ( Z ^ T ) )' % A)], 'breqtrd', '( %s -> %s <_ ( Z ^ T ) )' % (A, LS))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
zrp = w.s([zr, z0], 'elrpd', '( %s -> Z e. RR+ )' % A)
tzz = w.s([tn0], 'nn0zd', '( %s -> T e. ZZ )' % A)
zt = w.s([zrp, tzz], 'rpexpcld', '( %s -> ( Z ^ T ) e. RR+ )' % A)
bi = w.s([lrp, zt, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ ( Z ^ T ) <-> ( log ` %s ) <_ ( log ` ( Z ^ T ) ) ) )' % (A, LS, LS))
ll = w.s([ub2, bi], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` ( Z ^ T ) ) )' % (A, LS))
tz = w.s([tn0], 'nn0zd', '( %s -> T e. ZZ )' % A)
re = w.s([zrp, tz, w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( Z ^ T ) ) = ( T x. ( log ` Z ) ) )' % A)
ll2 = w.s([ll, re], 'breqtrd', '( %s -> ( log ` %s ) <_ ( T x. ( log ` Z ) ) )' % (A, LS))
tr = w.s([tn0], 'nn0red', '( %s -> T e. RR )' % A)
tg0 = w.s([tn0], 'nn0ge0d', '( %s -> 0 <_ T )' % A)
lzr = w.s([zrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
r5 = w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % A)
r3 = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % A)
f5a = w.s([r5, ar], 'remulcld', '( %s -> ( 5 x. %s ) e. RR )' % (A, A2))
f3b = w.s([r3, br], 'remulcld', '( %s -> ( 3 x. %s ) e. RR )' % (A, A3))
m12 = w.s([tr, f5a, lzr, f3b, tg0, lz0, t5, lz3], 'lemul12ad',
          '( %s -> ( T x. ( log ` Z ) ) <_ ( ( 5 x. %s ) x. ( 3 x. %s ) ) )' % (A, A2, A3))
c5 = w.s([w.s([], '5cn', '5 e. CC')], 'a1i', '( %s -> 5 e. CC )' % A)
c3 = w.s([w.s([], '3cn', '3 e. CC')], 'a1i', '( %s -> 3 e. CC )' % A)
ac = w.s([ar], 'recnd', '( %s -> %s e. CC )' % (A, A2))
bc = w.s([br], 'recnd', '( %s -> %s e. CC )' % (A, A3))
m4 = w.s([w.s([c5, ac], 'jca', '( %s -> ( 5 e. CC /\\ %s e. CC ) )' % (A, A2)),
          w.s([c3, bc], 'jca', '( %s -> ( 3 e. CC /\\ %s e. CC ) )' % (A, A3)), w.inst('mul4')], 'syl2anc',
         '( %s -> ( ( 5 x. %s ) x. ( 3 x. %s ) ) = ( ( 5 x. 3 ) x. ( %s x. %s ) ) )' % (A, A2, A3, A2, A3))
n15 = w.s([num.mul_nat(w, 5, 3)], 'a1i', '( %s -> ( 5 x. 3 ) = ; 1 5 )' % A)
m4b = w.s([m4, w.s([n15], 'oveq1d', '( %s -> ( ( 5 x. 3 ) x. ( %s x. %s ) ) = ( ; 1 5 x. ( %s x. %s ) ) )' % (A, A2, A3, A2, A3))], 'eqtrd',
          '( %s -> ( ( 5 x. %s ) x. ( 3 x. %s ) ) = ( ; 1 5 x. ( %s x. %s ) ) )' % (A, A2, A3, A2, A3))
m5 = w.s([m12, m4b], 'breqtrd', '( %s -> ( T x. ( log ` Z ) ) <_ ( ; 1 5 x. ( %s x. %s ) ) )' % (A, A2, A3))
llr = w.s([lrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (A, LS))
tlzr = w.s([tr, lzr], 'remulcld', '( %s -> ( T x. ( log ` Z ) ) e. RR )' % A)
abr = w.s([ar, br], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A, A2, A3))
m6 = w.s([llr, tlzr, w.s([w.s([num.fact(w, '; 1 5', 'RR')], 'a1i', '( %s -> ; 1 5 e. RR )' % A), abr], 'remulcld',
                         '( %s -> ( ; 1 5 x. ( %s x. %s ) ) e. RR )' % (A, A2, A3)), ll2, m5], 'letrd',
         '( %s -> ( log ` %s ) <_ ( ; 1 5 x. ( %s x. %s ) ) )' % (A, LS, A2, A3))
xv = w.s([sfn0, w.inst('xceilval')], 'syl', '( %s -> %s = ( %s ^ 5 ) )' % (A, XCS, LS))
z5 = w.s([num.fact(w, '5', 'ZZ')], 'a1i', '( %s -> 5 e. ZZ )' % A)
lx = w.s([lrp, z5, w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( %s ^ 5 ) ) = ( 5 x. ( log ` %s ) ) )' % (A, LS, LS))
lx2 = w.s([w.s([xv], 'fveq2d', '( %s -> ( log ` %s ) = ( log ` ( %s ^ 5 ) ) )' % (A, XCS, LS)), lx], 'eqtrd',
          '( %s -> ( log ` %s ) = ( 5 x. ( log ` %s ) ) )' % (A, XCS, LS))
fin = linarith(w, A, [m6], '( 5 x. ( log ` %s ) ) <_ ( ; 7 5 x. ( %s x. %s ) )' % (LS, A2, A3),
               leaves={'( log ` %s )' % LS: llr, '( %s x. %s )' % (A2, A3): abr})
w.qed([lx2, fin], 'eqbrtrd', '( %s -> ( log ` %s ) <_ ( ; 7 5 x. ( %s x. %s ) ) )' % (A, XCS, A2, A3))
run(w)

# ------------------------------------------------------------------ s3recip
PSET = '( ( ( W + 1 ) ... Z ) i^i Prime )'
RHS = '( ( ( ( log ` Z ) - ( log ` W ) ) + R ) / ( log ` W ) )'
RB = lambda v, u: 'sum_ i e. ( ( ( %s + 1 ) ... %s ) i^i Prime ) ( 1 / i ) <_ ( ( ( ( log ` %s ) - ( log ` %s ) ) + R ) / ( log ` %s ) )' % (v, u, u, v, v)
RECIP = 'A. v e. ( ZZ>= ` 2 ) A. u e. ( ZZ>= ` v ) %s' % RB('v', 'u')

w = WH('s3recip', 'The reciprocal sum of the reservoir primes is at most 3 / 160 (Lean: Step3W.lean hsum_Q; from recipsum).')
zn0 = w.h('Z e. NN0'); wn0 = w.h('W e. NN0'); yn0 = w.h('Y e. NN0')
sub = w.h('S C_ %s' % GPW)
w2 = w.h('W e. ( ZZ>= ` 2 )')
zw = w.h('Z e. ( ZZ>= ` W )')
rr = w.h('R e. RR')
rec = w.h(RECIP)
lw = w.h('( ( ; 9 9 / ; ; 1 0 0 ) x. ( log ` Z ) ) <_ ( ( log ` W ) + 1 )')
lzb = w.h('( ; ; 2 0 0 x. ( ( abs ` R ) + 2 ) ) <_ ( log ` Z )')
A = 'ph'
ty = w.s([zn0, wn0, yn0], '3jca', '( %s -> %s )' % (A, TY))
tysub = w.s([ty, sub], 'jca', '( %s -> ( %s /\\ S C_ %s ) )' % (A, TY, GPW))
sfp = w.s([tysub, w.inst('s3sfp')], 'syl', '( %s -> S e. %s )' % (A, FP))
sprm = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % A)], 'simpld', '( %s -> S C_ Prime )' % A)
al = w.s([tysub, w.inst('s3sall')], 'syl', '( %s -> A. r e. S ( r <_ Z /\\ W < r ) )' % A)
wnn = w.s([w2, w.inst('eluz2nn')], 'syl', '( %s -> W e. NN )' % A)
wrp = w.s([wnn], 'nnrpd', '( %s -> W e. RR+ )' % A)
wz = w.s([wnn], 'nnzd', '( %s -> W e. ZZ )' % A)
z2 = w.s([zw, w2, w.inst('uztrn')], 'syl2anc', '( %s -> Z e. ( ZZ>= ` 2 ) )' % A)
znn = w.s([z2, w.inst('eluz2nn')], 'syl', '( %s -> Z e. NN )' % A)
zrp = w.s([znn], 'nnrpd', '( %s -> Z e. RR+ )' % A)
zz = w.s([znn], 'nnzd', '( %s -> Z e. ZZ )' % A)
lwr = w.s([wrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` W ) e. RR )' % A)
lzr = w.s([zrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
w1 = w.s([w2, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < W )' % A)
lw0 = w.s([w1, w.s([wrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < ( log ` W ) <-> 1 < W ) )' % A)], 'mpbird', '( %s -> 0 < ( log ` W ) )' % A)
lwrp = w.s([lwr, lw0], 'elrpd', '( %s -> ( log ` W ) e. RR+ )' % A)
# S C_ PSET
B = '( %s /\\ r e. S )' % A
rin = w.s([], 'simpr', '( %s -> r e. S )' % B)
rprm = w.s([w.s([sprm], 'adantr', '( %s -> S C_ Prime )' % B), rin], 'sseldd', '( %s -> r e. Prime )' % B)
rb = w.s([w.s([al], 'adantr', '( %s -> A. r e. S ( r <_ Z /\\ W < r ) )' % B), rin, w.inst('rspa')], 'syl2anc',
         '( %s -> ( r <_ Z /\\ W < r ) )' % B)
rlez = w.s([rb], 'simpld', '( %s -> r <_ Z )' % B)
wltr = w.s([rb], 'simprd', '( %s -> W < r )' % B)
rz = w.s([w.s([rprm, w.inst('prmnn')], 'syl', '( %s -> r e. NN )' % B)], 'nnzd', '( %s -> r e. ZZ )' % B)
wp1 = w.s([wltr, w.s([w.s([wz], 'adantr', '( %s -> W e. ZZ )' % B), rz, w.inst('zltp1le')], 'syl2anc',
                     '( %s -> ( W < r <-> ( W + 1 ) <_ r ) )' % B)], 'mpbid', '( %s -> ( W + 1 ) <_ r )' % B)
wp1z = w.s([w.s([wz], 'adantr', '( %s -> W e. ZZ )' % B)], 'peano2zd', '( %s -> ( W + 1 ) e. ZZ )' % B)
fz1 = w.s([wp1z, w.s([zz], 'adantr', '( %s -> Z e. ZZ )' % B), rz], '3jca',
           '( %s -> ( ( W + 1 ) e. ZZ /\\ Z e. ZZ /\\ r e. ZZ ) )' % B)
fz2 = w.s([wp1, rlez], 'jca', '( %s -> ( ( W + 1 ) <_ r /\\ r <_ Z ) )' % B)
fz = w.s([fz1, fz2], 'jca', '( %s -> ( ( ( W + 1 ) e. ZZ /\\ Z e. ZZ /\\ r e. ZZ ) /\\ ( ( W + 1 ) <_ r /\\ r <_ Z ) ) )' % B)
infz = w.s([fz, w.inst('elfz2')], 'sylibr', '( %s -> r e. ( ( W + 1 ) ... Z ) )' % B)
inps = w.s([w.s([infz, rprm], 'jca', '( %s -> ( r e. ( ( W + 1 ) ... Z ) /\\ r e. Prime ) )' % B), w.inst('elin')], 'sylibr',
           '( %s -> r e. %s )' % (B, PSET))
ssp = w.s([w.s([inps], 'ex', '( %s -> ( r e. S -> r e. %s ) )' % (A, PSET))], 'ssrdv', '( %s -> S C_ %s )' % (A, PSET))
# fsumless
psfi = w.s([w.s([w.s([], 'fzfi', '( ( W + 1 ) ... Z ) e. Fin'), w.s([], 'inss1', '%s C_ ( ( W + 1 ) ... Z )' % PSET),
                 w.inst('ssfi')], 'mp2an', '%s e. Fin' % PSET)], 'a1i', '( %s -> %s e. Fin )' % (A, PSET))
C = '( %s /\\ q e. %s )' % (A, PSET)
qps = w.s([], 'simpr', '( %s -> q e. %s )' % (C, PSET))
qprm = w.s([w.s([w.s([], 'inss2', '%s C_ Prime' % PSET)], 'a1i', '( %s -> %s C_ Prime )' % (C, PSET)), qps], 'sseldd',
            '( %s -> q e. Prime )' % C)
qrp = w.s([w.s([qprm, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % C)], 'nnrpd', '( %s -> q e. RR+ )' % C)
qre = w.s([qrp, w.inst('rpreccl')], 'syl', '( %s -> ( 1 / q ) e. RR+ )' % C)
qrr = w.s([qre], 'rpred', '( %s -> ( 1 / q ) e. RR )' % C)
qg0 = w.s([qre], 'rpge0d', '( %s -> 0 <_ ( 1 / q ) )' % C)
fl = w.s([psfi, qrr, qg0, ssp], 'fsumless', '( %s -> sum_ q e. S ( 1 / q ) <_ sum_ q e. %s ( 1 / q ) )' % (A, PSET))
# recipsum at ( W , Z ]
idv = w.s([], 'id', '( v = W -> v = W )')
cg1, _b = w.wcongr('A. u e. ( ZZ>= ` v ) %s' % RB('v', 'u'), {'v': 'W'}, 'v = W', {'v': idv})
in1 = w.s([cg1, rec, w2], 'rspcdva', '( %s -> A. u e. ( ZZ>= ` W ) %s )' % (A, RB('W', 'u')))
idu = w.s([], 'id', '( u = Z -> u = Z )')
cg2, _b2 = w.wcongr(RB('W', 'u'), {'u': 'Z'}, 'u = Z', {'u': idu})
in2 = w.s([cg2, in1, zw], 'rspcdva', '( %s -> %s )' % (A, RB('W', 'Z')))
cb = w.s([w.s([], 'oveq2', '( i = q -> ( 1 / i ) = ( 1 / q ) )')], 'cbvsumv',
         'sum_ i e. %s ( 1 / i ) = sum_ q e. %s ( 1 / q )' % (PSET, PSET))
cbd = w.s([w.s([cb], 'a1i', '( %s -> sum_ i e. %s ( 1 / i ) = sum_ q e. %s ( 1 / q ) )' % (A, PSET, PSET))], 'eqcomd',
           '( %s -> sum_ q e. %s ( 1 / q ) = sum_ i e. %s ( 1 / i ) )' % (A, PSET, PSET))
in3 = w.s([cbd, in2], 'eqbrtrd',
          '( %s -> sum_ q e. %s ( 1 / q ) <_ %s )' % (A, PSET, RHS))
# the quotient is at most 3 / 160
q3 = w.s([num.fact(w, '( 3 / ; ; 1 6 0 )', 'RR')], 'a1i', '( %s -> ( 3 / ; ; 1 6 0 ) e. RR )' % A)
absr = w.s([rr], 'recnd', '( %s -> R e. CC )' % A)
absre = w.s([absr], 'abscld', '( %s -> ( abs ` R ) e. RR )' % A)
absge = w.s([absr], 'absge0d', '( %s -> 0 <_ ( abs ` R ) )' % A)
rle = w.s([rr], 'leabsd', '( %s -> R <_ ( abs ` R ) )' % A)
num_ = w.s([w.s([lzr, lwr], 'resubcld', '( %s -> ( ( log ` Z ) - ( log ` W ) ) e. RR )' % A), rr], 'readdcld',
           '( %s -> ( ( ( log ` Z ) - ( log ` W ) ) + R ) e. RR )' % A)
lin = linarith(w, A, [lw, lzb, rle, absge], '( ( ( log ` Z ) - ( log ` W ) ) + R ) <_ ( ( log ` W ) x. ( 3 / ; ; 1 6 0 ) )',
               leaves={'( log ` Z )': lzr, '( log ` W )': lwr, 'R': rr, '( abs ` R )': absre})
bi = w.s([num_, q3, lwrp], 'ledivmuld',
         '( %s -> ( ( ( ( ( log ` Z ) - ( log ` W ) ) + R ) / ( log ` W ) ) <_ ( 3 / ; ; 1 6 0 ) <-> ( ( ( log ` Z ) - ( log ` W ) ) + R ) <_ ( ( log ` W ) x. ( 3 / ; ; 1 6 0 ) ) ) )' % A)
qle = w.s([lin, bi], 'mpbird', '( %s -> ( ( ( ( log ` Z ) - ( log ` W ) ) + R ) / ( log ` W ) ) <_ ( 3 / ; ; 1 6 0 ) )' % A)
sumr = w.s([psfi, qrr], 'fsumrecl', '( %s -> sum_ q e. %s ( 1 / q ) e. RR )' % (A, PSET))
sfi2 = w.s([w.s([sfp, w.inst('elfpw')], 'sylib', '( %s -> ( S C_ Prime /\\ S e. Fin ) )' % A)], 'simprd', '( %s -> S e. Fin )' % A)
D = '( %s /\\ q e. S )' % A
qprm2 = w.s([w.s([sprm], 'adantr', '( %s -> S C_ Prime )' % D), w.s([], 'simpr', '( %s -> q e. S )' % D)], 'sseldd', '( %s -> q e. Prime )' % D)
qrp2 = w.s([w.s([qprm2, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % D)], 'nnrpd', '( %s -> q e. RR+ )' % D)
qrr2 = w.s([w.s([qrp2, w.inst('rpreccl')], 'syl', '( %s -> ( 1 / q ) e. RR+ )' % D)], 'rpred', '( %s -> ( 1 / q ) e. RR )' % D)
sumsr = w.s([sfi2, qrr2], 'fsumrecl', '( %s -> sum_ q e. S ( 1 / q ) e. RR )' % A)
divr = w.s([num_, lwrp], 'rerpdivcld', '( %s -> ( ( ( ( log ` Z ) - ( log ` W ) ) + R ) / ( log ` W ) ) e. RR )' % A)
t1 = w.s([sumsr, sumr, divr, fl, in3], 'letrd', '( %s -> sum_ q e. S ( 1 / q ) <_ ( ( ( ( log ` Z ) - ( log ` W ) ) + R ) / ( log ` W ) ) )' % A)
w.qed([sumsr, divr, q3, t1, qle], 'letrd', '( %s -> sum_ q e. S ( 1 / q ) <_ ( 3 / ; ; 1 6 0 ) )' % A)
run(w)

# ------------------------------------------------------------------ s3zgea
w = WH('s3zgea', 'ell2 n <_ z at windowed scales.')
d = zctx(w)
zbasics(w, d)
idz = w.s([], 'id', '( %s <_ Z -> %s <_ Z )' % (A2, A2))
w.qed([d['alez'], idz], 'syl', '( ph -> %s <_ Z )' % A2)
run(w)

# ------------------------------------------------------------------ s3wlez
w = W('s3wlez', 'The reservoir floor w is at most z when the subset Q is nonempty.')
A = '( %s /\\ S C_ %s /\\ S =/= (/) )' % (TY, GPW)
ty = w.s([], 'simp1', '( %s -> %s )' % (A, TY))
ss = w.s([], 'simp2', '( %s -> S C_ %s )' % (A, GPW))
sne = w.s([], 'simp3', '( %s -> S =/= (/) )' % A)
B = '( %s /\\ q e. S )' % A
bn = w.s([w.s([w.s([ty], 'adantr', '( %s -> %s )' % (B, TY)), w.s([ss], 'adantr', '( %s -> S C_ %s )' % (B, GPW)),
               w.s([], 'simpr', '( %s -> q e. S )' % B)], '3jca', '( %s -> ( %s /\\ S C_ %s /\\ q e. S ) )' % (B, TY, GPW)),
           w.inst('s3sbnd')], 'syl', '( %s -> ( q <_ Z /\\ W < q ) )' % B)
qz = w.s([bn], 'simpld', '( %s -> q <_ Z )' % B)
wq = w.s([bn], 'simprd', '( %s -> W < q )' % B)
zn0 = w.s([ty], 'simp1d', '( %s -> Z e. NN0 )' % A)
wn0 = w.s([ty], 'simp2d', '( %s -> W e. NN0 )' % A)
zr = w.s([w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)], 'adantr', '( %s -> Z e. RR )' % B)
wr = w.s([w.s([wn0], 'nn0red', '( %s -> W e. RR )' % A)], 'adantr', '( %s -> W e. RR )' % B)
qgp = w.s([w.s([ss], 'adantr', '( %s -> S C_ %s )' % (B, GPW)), w.s([], 'simpr', '( %s -> q e. S )' % B)], 'sseldd',
          '( %s -> q e. %s )' % (B, GPW))
gfi = w.s([w.s([ty], 'adantr', '( %s -> %s )' % (B, TY)), w.inst('goodprimeswfi')], 'syl', '( %s -> %s e. %s )' % (B, GPW, FP))
gprm = w.s([w.s([gfi, w.inst('elfpw')], 'sylib', '( %s -> ( %s C_ Prime /\\ %s e. Fin ) )' % (B, GPW, GPW))], 'simpld',
           '( %s -> %s C_ Prime )' % (B, GPW))
qre = w.s([w.s([w.s([gprm, qgp], 'sseldd', '( %s -> q e. Prime )' % B), w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % B)], 'nnred',
          '( %s -> q e. RR )' % B)
wz = linarith(w, B, [qz, wq], 'W <_ Z', leaves={'W': wr, 'q': qre, 'Z': zr})
ex = w.s([w.s([wz], 'ex', '( %s -> ( q e. S -> W <_ Z ) )' % A)], 'exlimdv', '( %s -> ( E. q q e. S -> W <_ Z ) )' % A)
n0 = w.s([sne, w.inst('n0')], 'sylib', '( %s -> E. q q e. S )' % A)
w.qed([n0, ex], 'mpd', '( %s -> W <_ Z )' % A)
run(w)

# ------------------------------------------------------------------- s3logw
Q99 = '( ; 9 9 / ; ; 1 0 0 )'
ZQ = '( Z ^c %s )' % Q99
w = WH('s3logw', 'The reservoir floor w has log w >_ ( 99 / 100 ) log z - 1 (Lean: Step3W.lean hlogw_lb, with log 2 < 1).')
zn0 = w.h('Z e. NN0'); z0 = w.h('0 < Z')
wn0 = w.h('W e. NN0'); w2 = w.h('2 <_ W')
wlo = w.h('%s <_ ( W + 1 )' % ZQ)
z3 = w.h('3 <_ %s' % ZQ)
A = 'ph'
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
zrp = w.s([zr, z0], 'elrpd', '( %s -> Z e. RR+ )' % A)
wr = w.s([wn0], 'nn0red', '( %s -> W e. RR )' % A)
w0 = linarith(w, A, [w2], '0 < W', leaves={'W': wr})
wrp = w.s([wr, w0], 'elrpd', '( %s -> W e. RR+ )' % A)
q99r = w.s([num.fact(w, Q99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, Q99))
zqrp = w.s([zrp, q99r], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, ZQ))
zqr = w.s([zqrp], 'rpred', '( %s -> %s e. RR )' % (A, ZQ))
half = linarith(w, A, [wlo, z3], '( %s / 2 ) <_ W' % ZQ, leaves={ZQ: zqr, 'W': wr})
r2 = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A)
hrp = w.s([zqrp, r2], 'rpdivcld', '( %s -> ( %s / 2 ) e. RR+ )' % (A, ZQ))
bi = w.s([hrp, wrp, w.inst('logleb')], 'syl2anc', '( %s -> ( ( %s / 2 ) <_ W <-> ( log ` ( %s / 2 ) ) <_ ( log ` W ) ) )' % (A, ZQ, ZQ))
ll = w.s([half, bi], 'mpbid', '( %s -> ( log ` ( %s / 2 ) ) <_ ( log ` W ) )' % (A, ZQ))
dv = w.s([zqrp, r2, w.inst('relogdiv')], 'syl2anc', '( %s -> ( log ` ( %s / 2 ) ) = ( ( log ` %s ) - ( log ` 2 ) ) )' % (A, ZQ, ZQ))
lc = w.s([zrp, q99r, w.inst('logcxp')], 'syl2anc', '( %s -> ( log ` %s ) = ( %s x. ( log ` Z ) ) )' % (A, ZQ, Q99))
dv2 = w.s([dv, w.s([lc], 'oveq1d', '( %s -> ( ( log ` %s ) - ( log ` 2 ) ) = ( ( %s x. ( log ` Z ) ) - ( log ` 2 ) ) )' % (A, ZQ, Q99))], 'eqtrd',
          '( %s -> ( log ` ( %s / 2 ) ) = ( ( %s x. ( log ` Z ) ) - ( log ` 2 ) ) )' % (A, ZQ, Q99))
ll2 = w.s([w.s([dv2], 'eqcomd', '( %s -> ( ( %s x. ( log ` Z ) ) - ( log ` 2 ) ) = ( log ` ( %s / 2 ) ) )' % (A, Q99, ZQ)), ll], 'eqbrtrd',
          '( %s -> ( ( %s x. ( log ` Z ) ) - ( log ` 2 ) ) <_ ( log ` W ) )' % (A, Q99))
l2 = w.s([w.s([], 'log2le1', '( log ` 2 ) < 1')], 'a1i', '( %s -> ( log ` 2 ) < 1 )' % A)
lzr = w.s([zrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
lwr = w.s([wrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` W ) e. RR )' % A)
l2r = w.s([r2, w.inst('relogcl')], 'syl', '( %s -> ( log ` 2 ) e. RR )' % A)
linarith(w, A, [ll2, l2], '( %s x. ( log ` Z ) ) <_ ( ( log ` W ) + 1 )' % Q99,
         leaves={'( log ` Z )': lzr, '( log ` W )': lwr, '( log ` 2 )': l2r}, name='qed')
run(w)
