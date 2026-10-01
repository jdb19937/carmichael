"""C7, Perron block 4: the far regime for U < 1 (pklt1h, pklt1v, pklt1) and the
indicator form pkind."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq

B0 = '( %s /\\ %s )' % (ULT1, CT)
UC = '( U ^c C )'
UFB = '( U ^c %s )' % FB
G0 = '( ( T ^ 2 ) x. %s )' % NLGU
TN = '( T x. %s )' % NLGU


def lt1ctx(w, A0, base):
    d = {}
    ul = w.s([base, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ULT1))
    ct = w.s([base, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, CT))
    d['urp'] = w.s([ul, w.inst('simpl')], 'syl', '( %s -> U e. RR+ )' % A0)
    d['u1'] = w.s([ul, w.inst('simpr')], 'syl', '( %s -> U < 1 )' % A0)
    d['crp'] = w.s([ct, w.inst('simpl')], 'syl', '( %s -> C e. RR+ )' % A0)
    d['trp'] = w.s([ct, w.inst('simpr')], 'syl', '( %s -> T e. RR+ )' % A0)
    d['une1'] = w.s([w.s([d['urp']], 'rpred', '( %s -> U e. RR )' % A0), d['u1']], 'ltned', '( %s -> U =/= 1 )' % A0)
    d['lr'] = w.s([d['urp'], w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, LGU))
    bi = w.s([d['urp'], a1(w, A0, '1rp', '1 e. RR+'), w.inst('logltb')], 'syl2anc', '( %s -> ( U < 1 <-> %s < ( log ` 1 ) ) )' % (A0, LGU))
    l1 = w.s([d['u1'], bi], 'mpbid', '( %s -> %s < ( log ` 1 ) )' % (A0, LGU))
    d['l0'] = w.s([l1, a1(w, A0, 'log1', '( log ` 1 ) = 0')], 'breqtrd', '( %s -> %s < 0 )' % (A0, LGU))
    d['nlrp'] = w.s([d['l0'], w.s([d['lr'], w.inst('negelrp')], 'syl', '( %s -> ( %s e. RR+ <-> %s < 0 ) )' % (A0, NLGU, LGU))], 'mpbird', '( %s -> %s e. RR+ )' % (A0, NLGU))
    fb = w.s([base, w.inst('farabs0')], 'syl', '( %s -> ( ( C + 1 ) <_ %s /\\ %s <_ ( %s / %s ) ) )' % (A0, FB, UFB, UC, G0))
    d['fb1'] = w.s([fb, w.inst('simpl')], 'syl', '( %s -> ( C + 1 ) <_ %s )' % (A0, FB))
    d['fb2'] = w.s([fb, w.inst('simpr')], 'syl', '( %s -> %s <_ ( %s / %s ) )' % (A0, UFB, UC, G0))
    cl = Closure(w, A0, {'U': ('RR+', d['urp']), 'C': ('RR+', d['crp']), 'T': ('RR+', d['trp']), LGU: [('RR', d['lr'])], NLGU: ('RR+', d['nlrp'])})
    cl.atom(LGU); cl.atom(NLGU)
    d['cl'] = cl
    d['fbr'] = cl.mem(FB, 'RR')
    d['fbge1'] = linarith(w, A0, [d['fb1'], cl.gt0('C')], '1 <_ %s' % FB, closure=cl)
    d['fb0'] = linarith(w, A0, [d['fb1'], cl.gt0('C')], '0 < %s' % FB, closure=cl)
    d['cle'] = linarith(w, A0, [d['fb1']], 'C <_ %s' % FB, closure=cl)
    d['fbrp'] = w.s([d['fbr'], d['fb0']], 'elrpd', '( %s -> %s e. RR+ )' % (A0, FB))
    d['fbne'] = w.s([d['fbrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, FB))
    cl.have(FB, 'RR+', d['fbrp']); cl.have(FB, 'gt0', d['fb0'])
    d['ucrp'] = w.s([d['urp'], cl.mem('C', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UC))
    d['ufbrp'] = w.s([d['urp'], d['fbr']], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UFB))
    cl.have(UC, 'RR+', d['ucrp']); cl.have(UFB, 'RR+', d['ufbrp']); cl.atom(UC); cl.atom(UFB)
    d['tnrp'] = w.s([d['trp'], d['nlrp']], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, TN))
    d['bnd'] = w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), d['ucrp']], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A0, UC)), d['tnrp']], 'rpdivcld',
                   '( %s -> %s e. RR+ )' % (A0, BND0))
    d['bndr'] = w.s([d['bnd']], 'rpred', '( %s -> %s e. RR )' % (A0, BND0))
    return d


# ---------------------------------------------------------------- pklt1h
HS = '( S e. RR /\\ ( abs ` S ) = T )'
A0 = '( %s /\\ %s )' % (B0, HS)
w = W('pklt1h', 'The two horizontal edges of Perron\'s far contour for ` U < 1 `, at height '
      '` S ` with ` |S| = T `, are each at most ` 2 U ^c C / ( T |log U| ) ` ( ~ hedgbnd , '
      '~ hedgbndr ); the exact edge integral is a quotient of two negatives.')
d = lt1ctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, B0)))
cl = d['cl']
sr = w.s([], 'simprl', '( %s -> S e. RR )' % A0)
sab = w.s([], 'simprr', '( %s -> ( abs ` S ) = T )' % A0)
sabrp = w.s([sab, d['trp']], 'eqeltrd', '( %s -> ( abs ` S ) e. RR+ )' % A0)
sc = w.s([sr], 'recnd', '( %s -> S e. CC )' % A0)
sne = w.s([w.s([w.s([w.s([sabrp], 'rpne0d', '( %s -> ( abs ` S ) =/= 0 )' % A0)], 'neneqd', '( %s -> -. ( abs ` S ) = 0 )' % A0),
                w.s([sc], 'abs00ad', '( %s -> ( ( abs ` S ) = 0 <-> S = 0 ) )' % A0)], 'mtbid', '( %s -> -. S = 0 )' % A0)], 'neqned', '( %s -> S =/= 0 )' % A0)
cr = cl.mem('C', 'RR')
hyp = w.s([w.s([w.s([d['urp'], d['une1']], 'jca', '( %s -> ( U e. RR+ /\\ U =/= 1 ) )' % A0),
                w.s([cr, d['fbr']], 'jca', '( %s -> ( C e. RR /\\ %s e. RR ) )' % (A0, FB))], 'jca',
               '( %s -> ( ( U e. RR+ /\\ U =/= 1 ) /\\ ( C e. RR /\\ %s e. RR ) ) )' % (A0, FB)),
           w.s([w.s([sr, sne], 'jca', '( %s -> ( S e. RR /\\ S =/= 0 ) )' % A0), d['cle']], 'jca', '( %s -> ( ( S e. RR /\\ S =/= 0 ) /\\ C <_ %s ) )' % (A0, FB))], 'jca',
          '( %s -> ( ( ( U e. RR+ /\\ U =/= 1 ) /\\ ( C e. RR /\\ %s e. RR ) ) /\\ ( ( S e. RR /\\ S =/= 0 ) /\\ C <_ %s ) ) )' % (A0, FB, FB))
HB = '( ( 1 / ( abs ` S ) ) x. ( ( %s - %s ) / %s ) )' % (UFB, UC, LGU)
h1 = w.s([hyp, w.inst('hedgbnd')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT('C', 'S'), CPT(FB, 'S')), HB))
h2 = w.s([hyp, w.inst('hedgbndr')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT(FB, 'S'), CPT('C', 'S')), HB))
# ( UFB - UC ) / L = ( UC - UFB ) / -u L
dif = '( %s - %s )' % (UFB, UC); ndif = '( %s - %s )' % (UC, UFB)
difc = w.s([cl.mem(dif, 'RR')], 'recnd', '( %s -> %s e. CC )' % (A0, dif))
lc = w.s([d['lr']], 'recnd', '( %s -> %s e. CC )' % (A0, LGU)); lne = w.s([d['l0']], 'lt0ne0d', '( %s -> %s =/= 0 )' % (A0, LGU))
ufc = w.s([d['ufbrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UFB)); ucc = w.s([d['ucrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC))
qe = w.s([w.s([w.s([difc, lc, lne], 'div2negd', '( %s -> ( -u %s / %s ) = ( %s / %s ) )' % (A0, dif, NLGU, dif, LGU))], 'eqcomd',
               '( %s -> ( %s / %s ) = ( -u %s / %s ) )' % (A0, dif, LGU, dif, NLGU)),
          w.s([w.s([ufc, ucc], 'negsubdi2d', '( %s -> -u %s = %s )' % (A0, dif, ndif))], 'oveq1d', '( %s -> ( -u %s / %s ) = ( %s / %s ) )' % (A0, dif, NLGU, ndif, NLGU))],
         'eqtrd', '( %s -> ( %s / %s ) = ( %s / %s ) )' % (A0, dif, LGU, ndif, NLGU))
ndle = linarith(w, A0, [cl.gt0(UFB), cl.gt0(UC)], '%s <_ ( 2 x. %s )' % (ndif, UC), closure=cl)
q1 = w.s([cl.mem(ndif, 'RR'), cl.mem('( 2 x. %s )' % UC, 'RR'), d['nlrp'], ndle], 'lediv1dd',
         '( %s -> ( %s / %s ) <_ ( ( 2 x. %s ) / %s ) )' % (A0, ndif, NLGU, UC, NLGU))
rt = w.s([d['trp']], 'rpreccld', '( %s -> ( 1 / T ) e. RR+ )' % A0)
Y = '( ( 2 x. %s ) / %s )' % (UC, NLGU)
q2 = w.s([cl.mem('( %s / %s )' % (ndif, NLGU), 'RR'), cl.mem(Y, 'RR'), w.s([rt], 'rpred', '( %s -> ( 1 / T ) e. RR )' % A0),
          w.s([rt], 'rpge0d', '( %s -> 0 <_ ( 1 / T ) )' % A0), q1], 'lemul2ad',
         '( %s -> ( ( 1 / T ) x. ( %s / %s ) ) <_ ( ( 1 / T ) x. %s ) )' % (A0, ndif, NLGU, Y))
yc = w.s([cl.mem(Y, 'RR')], 'recnd', '( %s -> %s e. CC )' % (A0, Y))
tc = w.s([cl.mem('T', 'RR')], 'recnd', '( %s -> T e. CC )' % A0); tne = w.s([d['trp']], 'rpne0d', '( %s -> T =/= 0 )' % A0)
nlc = w.s([d['nlrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, NLGU)); nlne = w.s([d['nlrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, NLGU))
a1_ = w.s([w.s([rt], 'rpcnd', '( %s -> ( 1 / T ) e. CC )' % A0), yc], 'mulcomd', '( %s -> ( ( 1 / T ) x. %s ) = ( %s x. ( 1 / T ) ) )' % (A0, Y, Y))
a2_ = w.s([w.s([yc, tc, tne], 'divrecd', '( %s -> ( %s / T ) = ( %s x. ( 1 / T ) ) )' % (A0, Y, Y))], 'eqcomd', '( %s -> ( %s x. ( 1 / T ) ) = ( %s / T ) )' % (A0, Y, Y))
uc2 = w.s([cl.mem('( 2 x. %s )' % UC, 'RR')], 'recnd', '( %s -> ( 2 x. %s ) e. CC )' % (A0, UC))
a3_ = w.s([uc2, nlc, tc, nlne, tne], 'divdiv1d', '( %s -> ( %s / T ) = ( ( 2 x. %s ) / ( %s x. T ) ) )' % (A0, Y, UC, NLGU))
a4_ = w.s([w.s([nlc, tc], 'mulcomd', '( %s -> ( %s x. T ) = %s )' % (A0, NLGU, TN))], 'oveq2d', '( %s -> ( ( 2 x. %s ) / ( %s x. T ) ) = %s )' % (A0, UC, NLGU, BND0))
alg = w.s([w.s([a1_, a2_], 'eqtrd', '( %s -> ( ( 1 / T ) x. %s ) = ( %s / T ) )' % (A0, Y, Y)), w.s([a3_, a4_], 'eqtrd', '( %s -> ( %s / T ) = %s )' % (A0, Y, BND0))],
          'eqtrd', '( %s -> ( ( 1 / T ) x. %s ) = %s )' % (A0, Y, BND0))
q3 = w.s([q2, alg], 'breqtrd', '( %s -> ( ( 1 / T ) x. ( %s / %s ) ) <_ %s )' % (A0, ndif, NLGU, BND0))
hbeq = w.s([w.s([sab], 'oveq2d', '( %s -> ( 1 / ( abs ` S ) ) = ( 1 / T ) )' % A0), qe], 'oveq12d', '( %s -> %s = ( ( 1 / T ) x. ( %s / %s ) ) )' % (A0, HB, ndif, NLGU))
hble = w.s([hbeq, q3], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, HB, BND0))
hbr2 = w.s([hbeq, cl.mem('( ( 1 / T ) x. ( %s / %s ) )' % (ndif, NLGU), 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, HB))
fcn = pkfcn_(w, A0, d['urp'])
ss = segh(w, A0, 'S', 'C', FB, sr, sne, cr, d['fbr'])
ac = cptcl(w, A0, 'C', 'S', cr, sr); bc = cptcl(w, A0, FB, 'S', d['fbr'], sr)
e1cl, _ = edgecl(w, A0, CPT('C', 'S'), CPT(FB, 'S'), ac, bc, fcn, ss)
ssr = w.s([w.s([w.s([bc, ac], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CPT(FB, 'S'), CPT('C', 'S'))), w.inst('csegcom')], 'syl',
               '( %s -> ( %s cseg %s ) = ( %s cseg %s ) )' % (A0, CPT(FB, 'S'), CPT('C', 'S'), CPT('C', 'S'), CPT(FB, 'S'))), ss], 'eqsstrd',
          '( %s -> ( %s cseg %s ) C_ %s )' % (A0, CPT(FB, 'S'), CPT('C', 'S'), DOM))
e2cl, _ = edgecl(w, A0, CPT(FB, 'S'), CPT('C', 'S'), bc, ac, fcn, ssr)
r1 = w.s([w.s([e1cl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E(CPT('C', 'S'), CPT(FB, 'S')))), hbr2, d['bndr'], h1, hble], 'letrd',
         '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT('C', 'S'), CPT(FB, 'S')), BND0))
r2 = w.s([w.s([e2cl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E(CPT(FB, 'S'), CPT('C', 'S')))), hbr2, d['bndr'], h2, hble], 'letrd',
         '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT(FB, 'S'), CPT('C', 'S')), BND0))
w.qed([r1, r2], 'jca', '( %s -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (A0, E(CPT('C', 'S'), CPT(FB, 'S')), BND0, E(CPT(FB, 'S'), CPT('C', 'S')), BND0))
run7(w)

# ---------------------------------------------------------------- pklt1v
A0 = B0
w = W('pklt1v', 'The far vertical edge of Perron\'s pole-free contour for ` U < 1 `, at the '
      'abscissa ` B ` with ` U ^c B <_ U ^c C / ( T ^ 2 |log U| ) ` ( ~ farabs0 ), is at most '
      '` 2 U ^c C / ( T |log U| ) ` ( ~ vedgbnd ).')
d = lt1ctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
cl = d['cl']
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
hyp = w.s([w.s([d['urp'], w.s([d['fbr'], d['fbne']], 'jca', '( %s -> ( %s e. RR /\\ %s =/= 0 ) )' % (A0, FB, FB))], 'jca',
               '( %s -> ( U e. RR+ /\\ ( %s e. RR /\\ %s =/= 0 ) ) )' % (A0, FB, FB)),
           w.s([ntr, tr], 'jca', '( %s -> ( -u T e. RR /\\ T e. RR ) )' % A0)], 'jca',
          '( %s -> ( ( U e. RR+ /\\ ( %s e. RR /\\ %s =/= 0 ) ) /\\ ( -u T e. RR /\\ T e. RR ) ) )' % (A0, FB, FB))
PA = CPT(FB, '-u T'); PB = CPT(FB, 'T')
VB = '( ( %s / ( abs ` %s ) ) x. ( abs ` ( %s - %s ) ) )' % (UFB, FB, PB, PA)
v1 = w.s([hyp, w.inst('vedgbnd')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(PA, PB), VB))
absf = w.s([d['fbr'], w.s([d['fbrp']], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, FB))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A0, FB, FB))
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0); ntc = w.s([ntr], 'recnd', '( %s -> -u T e. CC )' % A0)
fbc = w.s([d['fbr']], 'recnd', '( %s -> %s e. CC )' % (A0, FB))
dif = vdiff(w, A0, FB, '-u T', 'T', fbc, ntc, tc)
absd = w.s([w.s([dif], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( T - -u T ) ) ) )' % (A0, PB, PA)),
            absi_(w, A0, '( T - -u T )', w.s([tc, ntc], 'subcld', '( %s -> ( T - -u T ) e. CC )' % A0))], 'eqtrd',
           '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( T - -u T ) ) )' % (A0, PB, PA))
t2 = w.s([w.s([w.s([tc, tc], 'subnegd', '( %s -> ( T - -u T ) = ( T + T ) )' % A0), w.s([w.s([tc], '2timesd', '( %s -> ( 2 x. T ) = ( T + T ) )' % A0)], 'eqcomd', '( %s -> ( T + T ) = ( 2 x. T ) )' % A0)],
               'eqtrd', '( %s -> ( T - -u T ) = ( 2 x. T ) )' % A0)], 'fveq2d', '( %s -> ( abs ` ( T - -u T ) ) = ( abs ` ( 2 x. T ) ) )' % A0)
t2rp = w.s([a1(w, A0, '2rp', '2 e. RR+'), d['trp']], 'rpmulcld', '( %s -> ( 2 x. T ) e. RR+ )' % A0)
t3 = w.s([w.s([t2rp], 'rpred', '( %s -> ( 2 x. T ) e. RR )' % A0), w.s([t2rp], 'rpge0d', '( %s -> 0 <_ ( 2 x. T ) )' % A0)], 'absidd', '( %s -> ( abs ` ( 2 x. T ) ) = ( 2 x. T ) )' % A0)
absd2 = w.s([absd, w.s([t2, t3], 'eqtrd', '( %s -> ( abs ` ( T - -u T ) ) = ( 2 x. T ) )' % A0)], 'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = ( 2 x. T ) )' % (A0, PB, PA))
vbeq = w.s([w.s([absf], 'oveq2d', '( %s -> ( %s / ( abs ` %s ) ) = ( %s / %s ) )' % (A0, UFB, FB, UFB, FB)), absd2], 'oveq12d',
           '( %s -> %s = ( ( %s / %s ) x. ( 2 x. T ) ) )' % (A0, VB, UFB, FB))
ufr = cl.mem(UFB, 'RR')
s1 = w.s([a1(w, A0, '1rp', '1 e. RR+'), d['fbrp'], ufr, w.s([d['ufbrp']], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, UFB)), d['fbge1']], 'lediv2ad',
         '( %s -> ( %s / %s ) <_ ( %s / 1 ) )' % (A0, UFB, FB, UFB))
s1b = w.s([s1, w.s([w.s([ufr], 'recnd', '( %s -> %s e. CC )' % (A0, UFB))], 'div1d', '( %s -> ( %s / 1 ) = %s )' % (A0, UFB, UFB))], 'breqtrd',
          '( %s -> ( %s / %s ) <_ %s )' % (A0, UFB, FB, UFB))
g0rp = w.s([w.s([d['trp'], a1(w, A0, '2z', '2 e. ZZ')], 'rpexpcld', '( %s -> ( T ^ 2 ) e. RR+ )' % A0), d['nlrp']], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, G0))
QG = '( %s / %s )' % (UC, G0)
qgr = w.s([w.s([d['ucrp'], g0rp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, QG))], 'rpred', '( %s -> %s e. RR )' % (A0, QG))
s3 = w.s([cl.mem('( %s / %s )' % (UFB, FB), 'RR'), ufr, qgr, s1b, d['fb2']], 'letrd', '( %s -> ( %s / %s ) <_ %s )' % (A0, UFB, FB, QG))
s4 = w.s([cl.mem('( %s / %s )' % (UFB, FB), 'RR'), qgr, w.s([t2rp], 'rpred', '( %s -> ( 2 x. T ) e. RR )' % A0), w.s([t2rp], 'rpge0d', '( %s -> 0 <_ ( 2 x. T ) )' % A0), s3],
         'lemul1ad', '( %s -> ( ( %s / %s ) x. ( 2 x. T ) ) <_ ( %s x. ( 2 x. T ) ) )' % (A0, UFB, FB, QG))
# ( UC / G0 ) x. ( 2 T ) = ( 2 UC ) / TN
ucc = w.s([d['ucrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC)); t2c = w.s([t2rp], 'rpcnd', '( %s -> ( 2 x. T ) e. CC )' % A0)
g0c = w.s([g0rp], 'rpcnd', '( %s -> %s e. CC )' % (A0, G0)); g0ne = w.s([g0rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, G0))
b1 = w.s([w.s([ucc, t2c, g0c, g0ne], 'div23d', '( %s -> ( ( %s x. ( 2 x. T ) ) / %s ) = ( %s x. ( 2 x. T ) ) )' % (A0, UC, G0, QG))], 'eqcomd',
         '( %s -> ( %s x. ( 2 x. T ) ) = ( ( %s x. ( 2 x. T ) ) / %s ) )' % (A0, QG, UC, G0))
c2 = a1(w, A0, '2cn', '2 e. CC')
n1 = w.s([ucc, c2, tc], 'mul12d', '( %s -> ( %s x. ( 2 x. T ) ) = ( 2 x. ( %s x. T ) ) )' % (A0, UC, UC))
n2 = w.s([w.s([ucc, tc], 'mulcomd', '( %s -> ( %s x. T ) = ( T x. %s ) )' % (A0, UC, UC))], 'oveq2d', '( %s -> ( 2 x. ( %s x. T ) ) = ( 2 x. ( T x. %s ) ) )' % (A0, UC, UC))
n3 = w.s([c2, tc, ucc], 'mul12d', '( %s -> ( 2 x. ( T x. %s ) ) = ( T x. ( 2 x. %s ) ) )' % (A0, UC, UC))
num = w.s([w.s([n1, n2], 'eqtrd', '( %s -> ( %s x. ( 2 x. T ) ) = ( 2 x. ( T x. %s ) ) )' % (A0, UC, UC)), n3], 'eqtrd', '( %s -> ( %s x. ( 2 x. T ) ) = ( T x. ( 2 x. %s ) ) )' % (A0, UC, UC))
nlc = w.s([d['nlrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, NLGU))
den = w.s([w.s([w.s([tc], 'sqvald', '( %s -> ( T ^ 2 ) = ( T x. T ) )' % A0)], 'oveq1d', '( %s -> %s = ( ( T x. T ) x. %s ) )' % (A0, G0, NLGU)),
           w.s([tc, tc, nlc], 'mulassd', '( %s -> ( ( T x. T ) x. %s ) = ( T x. %s ) )' % (A0, NLGU, TN))], 'eqtrd', '( %s -> %s = ( T x. %s ) )' % (A0, G0, TN))
b2 = w.s([num, den], 'oveq12d', '( %s -> ( ( %s x. ( 2 x. T ) ) / %s ) = ( ( T x. ( 2 x. %s ) ) / ( T x. %s ) ) )' % (A0, UC, G0, UC, TN))
tnc = w.s([d['tnrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, TN)); tnne = w.s([d['tnrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, TN))
tne = w.s([d['trp']], 'rpne0d', '( %s -> T =/= 0 )' % A0)
uc2c = w.s([cl.mem('( 2 x. %s )' % UC, 'RR')], 'recnd', '( %s -> ( 2 x. %s ) e. CC )' % (A0, UC))
b3 = w.s([uc2c, tnc, tc, tnne, tne], 'divcan5d', '( %s -> ( ( T x. ( 2 x. %s ) ) / ( T x. %s ) ) = %s )' % (A0, UC, TN, BND0))
balg = w.s([b1, w.s([b2, b3], 'eqtrd', '( %s -> ( ( %s x. ( 2 x. T ) ) / %s ) = %s )' % (A0, UC, G0, BND0))], 'eqtrd', '( %s -> ( %s x. ( 2 x. T ) ) = %s )' % (A0, QG, BND0))
fin1 = w.s([s4, balg], 'breqtrd', '( %s -> ( ( %s / %s ) x. ( 2 x. T ) ) <_ %s )' % (A0, UFB, FB, BND0))
fcn = pkfcn_(w, A0, d['urp'])
ss = segv(w, A0, FB, '-u T', 'T', d['fbr'], d['fbne'], ntr, tr)
pac = cptcl(w, A0, FB, '-u T', d['fbr'], ntr); pbc = cptcl(w, A0, FB, 'T', d['fbr'], tr)
ecl, _ = edgecl(w, A0, PA, PB, pac, pbc, fcn, ss)
vbr = w.s([vbeq, cl.mem('( ( %s / %s ) x. ( 2 x. T ) )' % (UFB, FB), 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, VB))
w.qed([w.s([ecl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E(PA, PB))), vbr, d['bndr'], v1, w.s([vbeq, fin1], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, VB, BND0))],
      'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(PA, PB), BND0))
run7(w)

# ---------------------------------------------------------------- pklt1
A0 = B0
w = W('pklt1', 'The far-regime bound on the truncated Perron kernel for ` U < 1 `: the kernel '
      'line is at most ` 6 U ^c C / ( T |log U| ) `.  The contour is closed in the right '
      'half-plane at the far abscissa ( ~ pkrecid0c , ~ farabs0 ) and the three far edges are '
      'bounded ( ~ pklt1h , ~ pklt1v , ~ edgesol ).  This is ` norm_perronKernel_le_of_lt_one ` '
      'of Route Z\'s PerronKernel.lean, times ` 2 _pi `.')
d = lt1ctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
cl = d['cl']
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR'); cr = cl.mem('C', 'RR')
t0 = cl.gt0('T'); nt0 = linarith(w, A0, [t0], '-u T < 0', closure=cl); ntle = linarith(w, A0, [t0], '-u T <_ T', closure=cl)
E1 = E(CPT('C', '-u T'), CPT(FB, '-u T')); E2 = E(CPT(FB, '-u T'), CPT(FB, 'T')); E3 = E(CPT(FB, 'T'), CPT('C', 'T')); E4 = E(CPT('C', 'T'), CPT('C', '-u T'))
rid = w.s([d['urp'], w.s([w.s([cr, d['fbr']], 'jca', '( %s -> ( C e. RR /\\ %s e. RR ) )' % (A0, FB)), w.s([ntr, tr], 'jca', '( %s -> ( -u T e. RR /\\ T e. RR ) )' % A0)], 'jca',
                          '( %s -> ( ( C e. RR /\\ %s e. RR ) /\\ ( -u T e. RR /\\ T e. RR ) ) )' % (A0, FB)),
           w.s([w.s([d['cle'], ntle], 'jca', '( %s -> ( C <_ %s /\\ -u T <_ T ) )' % (A0, FB)), cl.gt0('C')], 'jca',
               '( %s -> ( ( C <_ %s /\\ -u T <_ T ) /\\ 0 < C ) )' % (A0, FB)), w.inst('pkrecid0c')], 'syl3anc',
          '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = 0 )' % (A0, E1, E2, E3, E4))
fcn = pkfcn_(w, A0, d['urp'])
nsne = w.s([nt0], 'lt0ne0d', '( %s -> -u T =/= 0 )' % A0); tne = w.s([d['trp']], 'rpne0d', '( %s -> T =/= 0 )' % A0); cne = w.s([d['crp']], 'rpne0d', '( %s -> C =/= 0 )' % A0)
p1 = cptcl(w, A0, 'C', '-u T', cr, ntr); p2 = cptcl(w, A0, FB, '-u T', d['fbr'], ntr); p3 = cptcl(w, A0, FB, 'T', d['fbr'], tr); p4 = cptcl(w, A0, 'C', 'T', cr, tr)
e1c, _ = edgecl(w, A0, CPT('C', '-u T'), CPT(FB, '-u T'), p1, p2, fcn, segh(w, A0, '-u T', 'C', FB, ntr, nsne, cr, d['fbr']))
e2c, _ = edgecl(w, A0, CPT(FB, '-u T'), CPT(FB, 'T'), p2, p3, fcn, segv(w, A0, FB, '-u T', 'T', d['fbr'], d['fbne'], ntr, tr))
ss3 = segh(w, A0, 'T', 'C', FB, tr, tne, cr, d['fbr'])
ss3r = w.s([w.s([w.s([p3, p4], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CPT(FB, 'T'), CPT('C', 'T'))), w.inst('csegcom')], 'syl',
                '( %s -> ( %s cseg %s ) = ( %s cseg %s ) )' % (A0, CPT(FB, 'T'), CPT('C', 'T'), CPT('C', 'T'), CPT(FB, 'T'))), ss3], 'eqsstrd',
           '( %s -> ( %s cseg %s ) C_ %s )' % (A0, CPT(FB, 'T'), CPT('C', 'T'), DOM))
e3c, _ = edgecl(w, A0, CPT(FB, 'T'), CPT('C', 'T'), p3, p4, fcn, ss3r)
# E4 = -u PK
sspk = segv(w, A0, 'C', '-u T', 'T', cr, cne, ntr, tr)
pkc, (abpk, fpk) = edgecl(w, A0, LO, HI, p1, p4, fcn, sspk)
rev = w.s([abpk, fpk, w.inst('lintrev')], 'syl2anc', '( %s -> %s = -u %s )' % (A0, E4, PK))
e4c = w.s([rev, w.s([pkc], 'negcld', '( %s -> -u %s e. CC )' % (A0, PK))], 'eqeltrd', '( %s -> %s e. CC )' % (A0, E4))
sol = w.s([w.s([w.s([w.s([e1c, e2c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, E1, E2)), w.s([e3c, e4c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, E3, E4))], 'jca',
                     '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, E1, E2, E3, E4)), a1(w, A0, '0cn', '0 e. CC')], 'jca',
                '( %s -> ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) /\\ 0 e. CC ) )' % (A0, E1, E2, E3, E4)), w.inst('edgesol')], 'syl',
          '( %s -> ( ( ( %s + %s ) + ( %s + %s ) ) = 0 -> ( abs ` ( %s - 0 ) ) <_ ( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) ) )' % (A0, E1, E2, E3, E4, E4, E1, E2, E3))
tri = w.s([rid, sol], 'mpd', '( %s -> ( abs ` ( %s - 0 ) ) <_ ( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A0, E4, E1, E2, E3))
ab4 = w.s([w.s([w.s([e4c], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A0, E4, E4))], 'fveq2d', '( %s -> ( abs ` ( %s - 0 ) ) = ( abs ` %s ) )' % (A0, E4, E4)),
           w.s([w.s([rev], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` -u %s ) )' % (A0, E4, PK)), w.s([pkc], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (A0, PK, PK))], 'eqtrd',
               '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, E4, PK))], 'eqtrd', '( %s -> ( abs ` ( %s - 0 ) ) = ( abs ` %s ) )' % (A0, E4, PK))
tri2 = w.s([ab4, tri], 'eqbrtrrd', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A0, PK, E1, E2, E3))
abst = w.s([tr, w.s([d['trp']], 'rpge0d', '( %s -> 0 <_ T )' % A0)], 'absidd', '( %s -> ( abs ` T ) = T )' % A0)
absnt = w.s([w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'absnegd', '( %s -> ( abs ` -u T ) = ( abs ` T ) )' % A0), abst], 'eqtrd', '( %s -> ( abs ` -u T ) = T )' % A0)
hT = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([tr, abst], 'jca', '( %s -> ( T e. RR /\\ ( abs ` T ) = T ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( T e. RR /\\ ( abs ` T ) = T ) ) )' % (A0, B0)),
          w.inst('pklt1h')], 'syl', '( %s -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (A0, E(CPT('C', 'T'), CPT(FB, 'T')), BND0, E3, BND0))
hnT = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([ntr, absnt], 'jca', '( %s -> ( -u T e. RR /\\ ( abs ` -u T ) = T ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( -u T e. RR /\\ ( abs ` -u T ) = T ) ) )' % (A0, B0)),
           w.inst('pklt1h')], 'syl', '( %s -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (A0, E1, BND0, E(CPT(FB, '-u T'), CPT('C', '-u T')), BND0))
b3 = w.s([hT, w.inst('simpr')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E3, BND0))
b1 = w.s([hnT, w.inst('simpl')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E1, BND0))
b2 = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('pklt1v')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E2, BND0))
a1e = w.s([e1c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E1)); a2 = w.s([e2c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E2)); a3 = w.s([e3c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E3))
cl.atom(BND0); cl.have(BND0, 'RR', d['bndr'])
for X, st in ((E1, a1e), (E2, a2), (E3, a3)):
    cl.atom('( abs ` %s )' % X); cl.have('( abs ` %s )' % X, 'RR', st)
s6 = linarith(w, A0, [b1, b2, b3], '( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) <_ ( 3 x. %s )' % (E1, E2, E3, BND0), closure=cl)
uc2c = w.s([cl.mem('( 2 x. %s )' % UC, 'RR')], 'recnd', '( %s -> ( 2 x. %s ) e. CC )' % (A0, UC))
tnc = w.s([d['tnrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, TN)); tnne = w.s([d['tnrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, TN))
ucc = w.s([d['ucrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC))
m1 = w.s([w.s([a1(w, A0, '3cn', '3 e. CC'), uc2c, tnc, tnne], 'divassd', '( %s -> ( ( 3 x. ( 2 x. %s ) ) / %s ) = ( 3 x. %s ) )' % (A0, UC, TN, BND0))], 'eqcomd',
         '( %s -> ( 3 x. %s ) = ( ( 3 x. ( 2 x. %s ) ) / %s ) )' % (A0, BND0, UC, TN))
m2 = w.s([w.s([w.s([a1(w, A0, '3cn', '3 e. CC'), a1(w, A0, '2cn', '2 e. CC'), ucc], 'mulassd', '( %s -> ( ( 3 x. 2 ) x. %s ) = ( 3 x. ( 2 x. %s ) ) )' % (A0, UC, UC))], 'eqcomd',
               '( %s -> ( 3 x. ( 2 x. %s ) ) = ( ( 3 x. 2 ) x. %s ) )' % (A0, UC, UC)),
          w.s([a1(w, A0, '3t2e6', '( 3 x. 2 ) = 6')], 'oveq1d', '( %s -> ( ( 3 x. 2 ) x. %s ) = ( 6 x. %s ) )' % (A0, UC, UC))], 'eqtrd', '( %s -> ( 3 x. ( 2 x. %s ) ) = ( 6 x. %s ) )' % (A0, UC, UC))
absl = w.s([w.s([d['lr'], w.s([d['lr'], d['l0']], 'ltled', '( %s -> %s <_ 0 )' % (A0, LGU)), w.inst('absnid')], 'syl2anc', '( %s -> ( abs ` %s ) = %s )' % (A0, LGU, NLGU))], 'eqcomd',
           '( %s -> %s = ( abs ` %s ) )' % (A0, NLGU, LGU))
m3 = w.s([m1, w.s([m2, w.s([absl], 'oveq2d', '( %s -> %s = ( T x. ( abs ` %s ) ) )' % (A0, TN, LGU))], 'oveq12d',
                   '( %s -> ( ( 3 x. ( 2 x. %s ) ) / %s ) = ( ( 6 x. %s ) / ( T x. ( abs ` %s ) ) ) )' % (A0, UC, TN, UC, LGU))], 'eqtrd',
         '( %s -> ( 3 x. %s ) = ( ( 6 x. %s ) / ( T x. ( abs ` %s ) ) ) )' % (A0, BND0, UC, LGU))
sumr = cl.mem('( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) )' % (E1, E2, E3), 'RR')
fin = w.s([w.s([pkc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, PK)), sumr, cl.mem('( 3 x. %s )' % BND0, 'RR'), tri2, s6], 'letrd', '( %s -> ( abs ` %s ) <_ ( 3 x. %s ) )' % (A0, PK, BND0))
w.qed([fin, m3], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( ( 6 x. %s ) / ( T x. ( abs ` %s ) ) ) )' % (A0, PK, UC, LGU))
run7(w)

# ---------------------------------------------------------------- pkind
A0 = '( ( U e. RR+ /\\ U =/= 1 ) /\\ %s )' % CT
IND = 'if ( 1 < U , %s , 0 )' % TPI
RHS = '( ( 6 x. %s ) / ( T x. ( abs ` %s ) ) )' % (UC, LGU)
w = W('pkind', 'The far-regime bound on the truncated Perron kernel with the indicator of '
      '` 1 < U `: ` norm_perronKernel_sub_indicator_le ` of Route Z\'s PerronKernel.lean, '
      'times ` 2 _pi ` ( ~ pkgt1 , ~ pklt1 ).')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0)
ct = w.s([], 'simpr', '( %s -> %s )' % (A0, CT))
ur = w.s([urp], 'rpred', '( %s -> U e. RR )' % A0)
A1 = '( %s /\\ 1 < U )' % A0
u1 = w.s([], 'simpr', '( %s -> 1 < U )' % A1)
g = w.s([w.s([w.s([w.s([ur], 'adantr', '( %s -> U e. RR )' % A1), u1], 'jca', '( %s -> %s )' % (A1, UGT1)), w.s([ct], 'adantr', '( %s -> %s )' % (A1, CT))], 'jca',
              '( %s -> ( %s /\\ %s ) )' % (A1, UGT1, CT)), w.inst('pkgt1')], 'syl', '( %s -> ( abs ` ( %s - %s ) ) <_ ( ( 6 x. %s ) / ( T x. %s ) ) )' % (A1, PK, TPI, UC, LGU))
ift = w.s([u1], 'iftrued', '( %s -> %s = %s )' % (A1, IND, TPI))
lge0 = w.s([w.s([ur], 'adantr', '( %s -> U e. RR )' % A1), w.s([a1(w, A1, '1re', '1 e. RR'), w.s([ur], 'adantr', '( %s -> U e. RR )' % A1), u1], 'ltled', '( %s -> 1 <_ U )' % A1), w.inst('logge0')], 'syl2anc',
           '( %s -> 0 <_ %s )' % (A1, LGU))
absl = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % A1), w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A1, LGU)), lge0], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A1, LGU, LGU))
c1 = w.s([w.s([w.s([ift], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (A1, PK, IND, PK, TPI))], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A1, PK, IND, PK, TPI)),
          w.s([g, w.s([w.s([w.s([absl], 'eqcomd', '( %s -> %s = ( abs ` %s ) )' % (A1, LGU, LGU))], 'oveq2d', '( %s -> ( T x. %s ) = ( T x. ( abs ` %s ) ) )' % (A1, LGU, LGU))], 'oveq2d',
                          '( %s -> ( ( 6 x. %s ) / ( T x. %s ) ) = %s )' % (A1, UC, LGU, RHS))], 'breqtrd', '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A1, PK, TPI, RHS))],
         'eqbrtrd', '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A1, PK, IND, RHS))
A2 = '( %s /\\ -. 1 < U )' % A0
nu1 = w.s([], 'simpr', '( %s -> -. 1 < U )' % A2)
ur2 = w.s([ur], 'adantr', '( %s -> U e. RR )' % A2)
ule = w.s([nu1, w.s([ur2, a1(w, A2, '1re', '1 e. RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( U <_ 1 <-> -. 1 < U ) )' % A2)], 'mpbird', '( %s -> U <_ 1 )' % A2)
ult = w.s([w.s([ule, w.s([w.s([une], 'adantr', '( %s -> U =/= 1 )' % A2)], 'necomd', '( %s -> 1 =/= U )' % A2)], 'jca', '( %s -> ( U <_ 1 /\\ 1 =/= U ) )' % A2),
           w.s([ur2, a1(w, A2, '1re', '1 e. RR'), w.inst('ltlen')], 'syl2anc', '( %s -> ( U < 1 <-> ( U <_ 1 /\\ 1 =/= U ) ) )' % A2)], 'mpbird', '( %s -> U < 1 )' % A2)
l = w.s([w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % A2), ult], 'jca', '( %s -> %s )' % (A2, ULT1)), w.s([ct], 'adantr', '( %s -> %s )' % (A2, CT))], 'jca',
              '( %s -> ( %s /\\ %s ) )' % (A2, ULT1, CT)), w.inst('pklt1')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A2, PK, RHS))
iff = w.s([nu1], 'iffalsed', '( %s -> %s = 0 )' % (A2, IND))
pkc = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % A2), w.s([w.s([ct], 'adantr', '( %s -> %s )' % (A2, CT)), w.inst('simpl')], 'syl', '( %s -> C e. RR+ )' % A2),
           w.s([w.s([ct], 'adantr', '( %s -> %s )' % (A2, CT)), w.inst('simpr')], 'syl', '( %s -> T e. RR+ )' % A2), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (A2, PK))
c2 = w.s([w.s([w.s([w.s([iff], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - 0 ) )' % (A2, PK, IND, PK)), w.s([pkc], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A2, PK, PK))], 'eqtrd',
                    '( %s -> ( %s - %s ) = %s )' % (A2, PK, IND, PK))], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` %s ) )' % (A2, PK, IND, PK)), l], 'eqbrtrd',
         '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A2, PK, IND, RHS))
w.qed([c1, c2], 'pm2.61dan', '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A0, PK, IND, RHS))
run7(w)
