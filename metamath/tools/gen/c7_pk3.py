"""C7, Perron block 3: the far regime for 1 < U (pkgt1h, pkgt1v, pkgt1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq

B0 = '( %s /\\ %s )' % (UGT1, CT)
NFA = '-u ' + FA
UC = '( U ^c C )'
UNF = '( U ^c %s )' % NFA
UFA = '( U ^c %s )' % FA
G = '( ( T ^ 2 ) x. %s )' % LGU
TL = '( T x. %s )' % LGU


def gt1ctx(w, A0, base):
    """common facts under A0, where base proves ( A0 -> B0 )"""
    d = {}
    ug = w.s([base, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, UGT1))
    ct = w.s([base, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, CT))
    d['ur'] = w.s([ug, w.inst('simpl')], 'syl', '( %s -> U e. RR )' % A0)
    d['u1'] = w.s([ug, w.inst('simpr')], 'syl', '( %s -> 1 < U )' % A0)
    d['crp'] = w.s([ct, w.inst('simpl')], 'syl', '( %s -> C e. RR+ )' % A0)
    d['trp'] = w.s([ct, w.inst('simpr')], 'syl', '( %s -> T e. RR+ )' % A0)
    d['u0'] = w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), d['ur'], a1(w, A0, '0lt1', '0 < 1'), d['u1']], 'lttrd', '( %s -> 0 < U )' % A0)
    d['urp'] = w.s([d['ur'], d['u0']], 'elrpd', '( %s -> U e. RR+ )' % A0)
    d['lrp'] = w.s([d['ur'], d['u1'], w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A0, LGU))
    fa = w.s([w.s([ug, d['trp']], 'jca', '( %s -> ( %s /\\ T e. RR+ ) )' % (A0, UGT1)), w.inst('farabs')], 'syl',
             '( %s -> ( 1 <_ %s /\\ %s <_ %s ) )' % (A0, FA, G, UFA))
    d['fa1'] = w.s([fa, w.inst('simpl')], 'syl', '( %s -> 1 <_ %s )' % (A0, FA))
    d['fa2'] = w.s([fa, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, G, UFA))
    cl = Closure(w, A0, {'U': ('RR+', d['urp']), 'C': ('RR+', d['crp']), 'T': ('RR+', d['trp']), LGU: ('RR+', d['lrp'])})
    d['cl'] = cl
    d['far'] = cl.mem(FA, 'RR')
    d['fa0'] = linarith(w, A0, [d['fa1']], '0 < %s' % FA, closure=cl)
    d['farp'] = w.s([d['far'], d['fa0']], 'elrpd', '( %s -> %s e. RR+ )' % (A0, FA))
    cl.have(FA, 'RR+', d['farp']); cl.have(FA, 'gt0', d['fa0'])
    d['nfar'] = cl.mem(NFA, 'RR')
    d['nfa0'] = linarith(w, A0, [d['fa0']], '%s < 0' % NFA, closure=cl)
    d['nfane'] = w.s([d['nfa0']], 'lt0ne0d', '( %s -> %s =/= 0 )' % (A0, NFA))
    d['ucrp'] = w.s([d['urp'], cl.mem('C', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UC))
    d['unfrp'] = w.s([d['urp'], d['nfar']], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UNF))
    d['ufarp'] = w.s([d['urp'], d['far']], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, UFA))
    cl.have(UC, 'RR+', d['ucrp']); cl.have(UNF, 'RR+', d['unfrp']); cl.have(UFA, 'RR+', d['ufarp'])
    cl.atom(UC); cl.atom(UNF); cl.atom(UFA)
    d['tlrp'] = w.s([d['trp'], d['lrp']], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, TL))
    d['bnd'] = w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), d['ucrp']], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A0, UC)), d['tlrp']], 'rpdivcld',
                   '( %s -> %s e. RR+ )' % (A0, BND1))
    d['bndr'] = w.s([d['bnd']], 'rpred', '( %s -> %s e. RR )' % (A0, BND1))
    return d


# ---------------------------------------------------------------- pkgt1h
HS = '( S e. RR /\\ ( abs ` S ) = T )'
A0 = '( %s /\\ %s )' % (B0, HS)
w = W('pkgt1h', 'The two horizontal edges of Perron\'s far contour for ` 1 < U `, at height '
      '` S ` with ` |S| = T `, are each at most ` 2 U ^c C / ( T log U ) ` ( ~ hedgbnd , '
      '~ hedgbndr ): the sharper ` U ^c C - U ^c -u A <_ U ^c C ` replaces Lean\'s two steps.')
d = gt1ctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, B0)))
cl = d['cl']
sr = w.s([], 'simprl', '( %s -> S e. RR )' % A0)
sab = w.s([], 'simprr', '( %s -> ( abs ` S ) = T )' % A0)
sabrp = w.s([sab, d['trp']], 'eqeltrd', '( %s -> ( abs ` S ) e. RR+ )' % A0)
sc = w.s([sr], 'recnd', '( %s -> S e. CC )' % A0)
sne = w.s([w.s([w.s([sabrp], 'rpne0d', '( %s -> ( abs ` S ) =/= 0 )' % A0)], 'neneqd', '( %s -> -. ( abs ` S ) = 0 )' % A0),
           w.s([sc], 'abs00ad', '( %s -> ( ( abs ` S ) = 0 <-> S = 0 ) )' % A0)], 'mtbid', '( %s -> -. S = 0 )' % A0)
sne = w.s([sne], 'neqned', '( %s -> S =/= 0 )' % A0)
nfale = linarith(w, A0, [d['fa0'], cl.gt0('C')], '%s <_ C' % NFA, closure=cl)
hyp = w.s([w.s([w.s([d['urp'], w.s([d['u1']], 'gtned', '( %s -> U =/= 1 )' % A0)], 'jca', '( %s -> ( U e. RR+ /\\ U =/= 1 ) )' % A0),
                w.s([d['nfar'], cl.mem('C', 'RR')], 'jca', '( %s -> ( %s e. RR /\\ C e. RR ) )' % (A0, NFA))], 'jca',
               '( %s -> ( ( U e. RR+ /\\ U =/= 1 ) /\\ ( %s e. RR /\\ C e. RR ) ) )' % (A0, NFA)),
           w.s([w.s([sr, sne], 'jca', '( %s -> ( S e. RR /\\ S =/= 0 ) )' % A0), nfale], 'jca', '( %s -> ( ( S e. RR /\\ S =/= 0 ) /\\ %s <_ C ) )' % (A0, NFA))], 'jca',
          '( %s -> ( ( ( U e. RR+ /\\ U =/= 1 ) /\\ ( %s e. RR /\\ C e. RR ) ) /\\ ( ( S e. RR /\\ S =/= 0 ) /\\ %s <_ C ) ) )' % (A0, NFA, NFA))
HB = '( ( 1 / ( abs ` S ) ) x. ( ( %s - %s ) / %s ) )' % (UC, UNF, LGU)
h1 = w.s([hyp, w.inst('hedgbnd')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT(NFA, 'S'), CPT('C', 'S')), HB))
h2 = w.s([hyp, w.inst('hedgbndr')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT('C', 'S'), CPT(NFA, 'S')), HB))
# the bound comparison
dif = '( %s - %s )' % (UC, UNF)
difle = linarith(w, A0, [cl.gt0(UNF), cl.gt0(UC)], '%s <_ ( 2 x. %s )' % (dif, UC), closure=cl)
q1 = w.s([cl.mem(dif, 'RR'), cl.mem('( 2 x. %s )' % UC, 'RR'), d['lrp'], difle], 'lediv1dd',
         '( %s -> ( %s / %s ) <_ ( ( 2 x. %s ) / %s ) )' % (A0, dif, LGU, UC, LGU))
rt = w.s([d['trp']], 'rpreccld', '( %s -> ( 1 / T ) e. RR+ )' % A0)
q2 = w.s([cl.mem('( %s / %s )' % (dif, LGU), 'RR'), cl.mem('( ( 2 x. %s ) / %s )' % (UC, LGU), 'RR'), w.s([rt], 'rpred', '( %s -> ( 1 / T ) e. RR )' % A0),
          w.s([rt], 'rpge0d', '( %s -> 0 <_ ( 1 / T ) )' % A0), q1], 'lemul2ad',
         '( %s -> ( ( 1 / T ) x. ( %s / %s ) ) <_ ( ( 1 / T ) x. ( ( 2 x. %s ) / %s ) ) )' % (A0, dif, LGU, UC, LGU))
Y = '( ( 2 x. %s ) / %s )' % (UC, LGU)
yc = w.s([cl.mem(Y, 'RR')], 'recnd', '( %s -> %s e. CC )' % (A0, Y))
tc = w.s([cl.mem('T', 'RR')], 'recnd', '( %s -> T e. CC )' % A0); tne = w.s([d['trp']], 'rpne0d', '( %s -> T =/= 0 )' % A0)
lc = w.s([cl.mem(LGU, 'RR')], 'recnd', '( %s -> %s e. CC )' % (A0, LGU)); lne = w.s([d['lrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, LGU))
a1_ = w.s([w.s([rt], 'rpcnd', '( %s -> ( 1 / T ) e. CC )' % A0), yc], 'mulcomd', '( %s -> ( ( 1 / T ) x. %s ) = ( %s x. ( 1 / T ) ) )' % (A0, Y, Y))
a2_ = w.s([w.s([yc, tc, tne], 'divrecd', '( %s -> ( %s / T ) = ( %s x. ( 1 / T ) ) )' % (A0, Y, Y))], 'eqcomd', '( %s -> ( %s x. ( 1 / T ) ) = ( %s / T ) )' % (A0, Y, Y))
uc2 = w.s([cl.mem('( 2 x. %s )' % UC, 'RR')], 'recnd', '( %s -> ( 2 x. %s ) e. CC )' % (A0, UC))
a3_ = w.s([uc2, lc, tc, lne, tne], 'divdiv1d', '( %s -> ( %s / T ) = ( ( 2 x. %s ) / ( %s x. T ) ) )' % (A0, Y, UC, LGU))
a4_ = w.s([w.s([lc, tc], 'mulcomd', '( %s -> ( %s x. T ) = %s )' % (A0, LGU, TL))], 'oveq2d', '( %s -> ( ( 2 x. %s ) / ( %s x. T ) ) = %s )' % (A0, UC, LGU, BND1))
alg = w.s([w.s([a1_, a2_], 'eqtrd', '( %s -> ( ( 1 / T ) x. %s ) = ( %s / T ) )' % (A0, Y, Y)), w.s([a3_, a4_], 'eqtrd', '( %s -> ( %s / T ) = %s )' % (A0, Y, BND1))],
          'eqtrd', '( %s -> ( ( 1 / T ) x. %s ) = %s )' % (A0, Y, BND1))
q3 = w.s([q2, alg], 'breqtrd', '( %s -> ( ( 1 / T ) x. ( %s / %s ) ) <_ %s )' % (A0, dif, LGU, BND1))
hbeq = w.s([w.s([sab], 'oveq2d', '( %s -> ( 1 / ( abs ` S ) ) = ( 1 / T ) )' % A0)], 'oveq1d', '( %s -> %s = ( ( 1 / T ) x. ( %s / %s ) ) )' % (A0, HB, dif, LGU))
hble = w.s([hbeq, q3], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, HB, BND1))
hbr = cl.mem('( ( 1 / T ) x. ( %s / %s ) )' % (dif, LGU), 'RR')
hbr2 = w.s([hbeq, hbr], 'eqeltrd', '( %s -> %s e. RR )' % (A0, HB))
fcn = pkfcn_(w, A0, d['urp'])
ss = segh(w, A0, 'S', NFA, 'C', sr, sne, d['nfar'], cl.mem('C', 'RR'))
ac = cptcl(w, A0, NFA, 'S', d['nfar'], sr); bc = cptcl(w, A0, 'C', 'S', cl.mem('C', 'RR'), sr)
e1cl, (abp, fp) = edgecl(w, A0, CPT(NFA, 'S'), CPT('C', 'S'), ac, bc, fcn, ss)
ssr = w.s([w.s([w.s([bc, ac], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CPT('C', 'S'), CPT(NFA, 'S'))), w.inst('csegcom')], 'syl',
               '( %s -> ( %s cseg %s ) = ( %s cseg %s ) )' % (A0, CPT('C', 'S'), CPT(NFA, 'S'), CPT(NFA, 'S'), CPT('C', 'S'))), ss], 'eqsstrd',
          '( %s -> ( %s cseg %s ) C_ %s )' % (A0, CPT('C', 'S'), CPT(NFA, 'S'), DOM))
e2cl, _ = edgecl(w, A0, CPT('C', 'S'), CPT(NFA, 'S'), bc, ac, fcn, ssr)
r1 = w.s([w.s([e1cl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E(CPT(NFA, 'S'), CPT('C', 'S')))), hbr2, d['bndr'], h1, hble], 'letrd',
         '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT(NFA, 'S'), CPT('C', 'S')), BND1))
r2 = w.s([w.s([e2cl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E(CPT('C', 'S'), CPT(NFA, 'S')))), hbr2, d['bndr'], h2, hble], 'letrd',
         '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(CPT('C', 'S'), CPT(NFA, 'S')), BND1))
w.qed([r1, r2], 'jca', '( %s -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (A0, E(CPT(NFA, 'S'), CPT('C', 'S')), BND1, E(CPT('C', 'S'), CPT(NFA, 'S')), BND1))
run7(w)

# ---------------------------------------------------------------- pkgt1v
A0 = B0
w = W('pkgt1v', 'The far vertical edge of Perron\'s contour for ` 1 < U `, at the abscissa '
      '` -u A ` with ` T ^ 2 log U <_ U ^c A ` ( ~ farabs ), is at most ` 2 U ^c C / ( T log U ) ` '
      '( ~ vedgbnd ).')
d = gt1ctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
cl = d['cl']
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
hyp = w.s([w.s([d['urp'], w.s([d['nfar'], d['nfane']], 'jca', '( %s -> ( %s e. RR /\\ %s =/= 0 ) )' % (A0, NFA, NFA))], 'jca',
               '( %s -> ( U e. RR+ /\\ ( %s e. RR /\\ %s =/= 0 ) ) )' % (A0, NFA, NFA)),
           w.s([tr, ntr], 'jca', '( %s -> ( T e. RR /\\ -u T e. RR ) )' % A0)], 'jca',
          '( %s -> ( ( U e. RR+ /\\ ( %s e. RR /\\ %s =/= 0 ) ) /\\ ( T e. RR /\\ -u T e. RR ) ) )' % (A0, NFA, NFA))
PA = CPT(NFA, 'T'); PB = CPT(NFA, '-u T')
VB = '( ( %s / ( abs ` %s ) ) x. ( abs ` ( %s - %s ) ) )' % (UNF, NFA, PB, PA)
v1 = w.s([hyp, w.inst('vedgbnd')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(PA, PB), VB))
# abs -u FA = FA ;  abs ( PB - PA ) = 2 T
absn = w.s([w.s([w.s([d['far']], 'recnd', '( %s -> %s e. CC )' % (A0, FA))], 'absnegd', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, NFA, FA)),
            w.s([d['far'], w.s([d['farp']], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, FA))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A0, FA, FA))], 'eqtrd',
           '( %s -> ( abs ` %s ) = %s )' % (A0, NFA, FA))
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0); ntc = w.s([ntr], 'recnd', '( %s -> -u T e. CC )' % A0)
nfac = w.s([d['nfar']], 'recnd', '( %s -> %s e. CC )' % (A0, NFA))
dif = vdiff(w, A0, NFA, 'T', '-u T', nfac, tc, ntc)
absd = w.s([w.s([dif], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( -u T - T ) ) ) )' % (A0, PB, PA)),
            absi_(w, A0, '( -u T - T )', w.s([ntc, tc], 'subcld', '( %s -> ( -u T - T ) e. CC )' % A0))], 'eqtrd',
           '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( -u T - T ) ) )' % (A0, PB, PA))
t2 = w.s([w.s([ntc, tc], 'abssubd', '( %s -> ( abs ` ( -u T - T ) ) = ( abs ` ( T - -u T ) ) )' % A0),
          w.s([w.s([w.s([tc, tc], 'subnegd', '( %s -> ( T - -u T ) = ( T + T ) )' % A0), w.s([w.s([tc], '2timesd', '( %s -> ( 2 x. T ) = ( T + T ) )' % A0)], 'eqcomd', '( %s -> ( T + T ) = ( 2 x. T ) )' % A0)],
                    'eqtrd', '( %s -> ( T - -u T ) = ( 2 x. T ) )' % A0)], 'fveq2d', '( %s -> ( abs ` ( T - -u T ) ) = ( abs ` ( 2 x. T ) ) )' % A0)], 'eqtrd',
         '( %s -> ( abs ` ( -u T - T ) ) = ( abs ` ( 2 x. T ) ) )' % A0)
t2rp = w.s([a1(w, A0, '2rp', '2 e. RR+'), d['trp']], 'rpmulcld', '( %s -> ( 2 x. T ) e. RR+ )' % A0)
t3 = w.s([w.s([t2rp], 'rpred', '( %s -> ( 2 x. T ) e. RR )' % A0), w.s([t2rp], 'rpge0d', '( %s -> 0 <_ ( 2 x. T ) )' % A0)], 'absidd', '( %s -> ( abs ` ( 2 x. T ) ) = ( 2 x. T ) )' % A0)
absd2 = w.s([absd, w.s([t2, t3], 'eqtrd', '( %s -> ( abs ` ( -u T - T ) ) = ( 2 x. T ) )' % A0)], 'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = ( 2 x. T ) )' % (A0, PB, PA))
vbeq = w.s([w.s([absn], 'oveq2d', '( %s -> ( %s / ( abs ` %s ) ) = ( %s / %s ) )' % (A0, UNF, NFA, UNF, FA)), absd2], 'oveq12d',
           '( %s -> %s = ( ( %s / %s ) x. ( 2 x. T ) ) )' % (A0, VB, UNF, FA))
# ( UNF / FA ) <_ UNF <_ 1 / ( T ^ 2 L )
unfr = cl.mem(UNF, 'RR')
s1 = w.s([a1(w, A0, '1rp', '1 e. RR+'), d['farp'], unfr, w.s([d['unfrp']], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, UNF)), d['fa1']], 'lediv2ad',
         '( %s -> ( %s / %s ) <_ ( %s / 1 ) )' % (A0, UNF, FA, UNF))
s1b = w.s([s1, w.s([w.s([unfr], 'recnd', '( %s -> %s e. CC )' % (A0, UNF))], 'div1d', '( %s -> ( %s / 1 ) = %s )' % (A0, UNF, UNF))], 'breqtrd',
          '( %s -> ( %s / %s ) <_ %s )' % (A0, UNF, FA, UNF))
uc = w.s([d['urp']], 'rpcnd', '( %s -> U e. CC )' % A0); une = w.s([d['urp']], 'rpne0d', '( %s -> U =/= 0 )' % A0)
neg = w.s([uc, une, w.s([d['far']], 'recnd', '( %s -> %s e. CC )' % (A0, FA)), w.inst('cxpneg')], 'syl3anc', '( %s -> %s = ( 1 / %s ) )' % (A0, UNF, UFA))
grp = w.s([w.s([d['trp'], a1(w, A0, '2z', '2 e. ZZ')], 'rpexpcld', '( %s -> ( T ^ 2 ) e. RR+ )' % A0), d['lrp']], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, G))
s2 = w.s([grp, d['ufarp'], a1(w, A0, '1re', '1 e. RR'), a1(w, A0, '0le1', '0 <_ 1'), d['fa2']], 'lediv2ad', '( %s -> ( 1 / %s ) <_ ( 1 / %s ) )' % (A0, UFA, G))
rg = w.s([w.s([grp], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (A0, G))], 'rpred', '( %s -> ( 1 / %s ) e. RR )' % (A0, G))
s3 = w.s([cl.mem('( %s / %s )' % (UNF, FA), 'RR'), unfr, rg, s1b, w.s([neg, s2], 'eqbrtrd', '( %s -> %s <_ ( 1 / %s ) )' % (A0, UNF, G))], 'letrd',
         '( %s -> ( %s / %s ) <_ ( 1 / %s ) )' % (A0, UNF, FA, G))
s4 = w.s([cl.mem('( %s / %s )' % (UNF, FA), 'RR'), rg, w.s([t2rp], 'rpred', '( %s -> ( 2 x. T ) e. RR )' % A0), w.s([t2rp], 'rpge0d', '( %s -> 0 <_ ( 2 x. T ) )' % A0), s3],
         'lemul1ad', '( %s -> ( ( %s / %s ) x. ( 2 x. T ) ) <_ ( ( 1 / %s ) x. ( 2 x. T ) ) )' % (A0, UNF, FA, G))
# ( 1 / G ) x. ( 2 T ) = 2 / ( T L )
gc = w.s([grp], 'rpcnd', '( %s -> %s e. CC )' % (A0, G)); gne = w.s([grp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, G))
t2c = w.s([t2rp], 'rpcnd', '( %s -> ( 2 x. T ) e. CC )' % A0)
rgc = w.s([rg], 'recnd', '( %s -> ( 1 / %s ) e. CC )' % (A0, G))
b0 = w.s([rgc, t2c], 'mulcomd', '( %s -> ( ( 1 / %s ) x. ( 2 x. T ) ) = ( ( 2 x. T ) x. ( 1 / %s ) ) )' % (A0, G, G))
b1 = w.s([w.s([t2c, gc, gne], 'divrecd', '( %s -> ( ( 2 x. T ) / %s ) = ( ( 2 x. T ) x. ( 1 / %s ) ) )' % (A0, G, G))], 'eqcomd',
         '( %s -> ( ( 2 x. T ) x. ( 1 / %s ) ) = ( ( 2 x. T ) / %s ) )' % (A0, G, G))
lc = w.s([cl.mem(LGU, 'RR')], 'recnd', '( %s -> %s e. CC )' % (A0, LGU)); tc_ = tc
tlc = w.s([tc_, lc], 'mulcld', '( %s -> %s e. CC )' % (A0, TL)); tlne = w.s([d['tlrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, TL))
geq = w.s([w.s([w.s([tc_], 'sqvald', '( %s -> ( T ^ 2 ) = ( T x. T ) )' % A0)], 'oveq1d', '( %s -> %s = ( ( T x. T ) x. %s ) )' % (A0, G, LGU)),
           w.s([tc_, tc_, lc], 'mulassd', '( %s -> ( ( T x. T ) x. %s ) = ( T x. %s ) )' % (A0, LGU, TL))], 'eqtrd', '( %s -> %s = ( T x. %s ) )' % (A0, G, TL))
b2 = w.s([geq], 'oveq2d', '( %s -> ( ( 2 x. T ) / %s ) = ( ( 2 x. T ) / ( T x. %s ) ) )' % (A0, G, TL))
tne = w.s([d['trp']], 'rpne0d', '( %s -> T =/= 0 )' % A0)
b3 = w.s([w.s([w.s([a1(w, A0, '2cn', '2 e. CC'), tc_], 'mulcomd', '( %s -> ( 2 x. T ) = ( T x. 2 ) )' % A0)], 'oveq1d', '( %s -> ( ( 2 x. T ) / ( T x. %s ) ) = ( ( T x. 2 ) / ( T x. %s ) ) )' % (A0, TL, TL)),
          w.s([a1(w, A0, '2cn', '2 e. CC'), tlc, tc_, tlne, tne], 'divcan5d', '( %s -> ( ( T x. 2 ) / ( T x. %s ) ) = ( 2 / %s ) )' % (A0, TL, TL))], 'eqtrd',
         '( %s -> ( ( 2 x. T ) / ( T x. %s ) ) = ( 2 / %s ) )' % (A0, TL, TL))
balg = w.s([w.s([b0, b1], 'eqtrd', '( %s -> ( ( 1 / %s ) x. ( 2 x. T ) ) = ( ( 2 x. T ) / %s ) )' % (A0, G, G)), w.s([b2, b3], 'eqtrd', '( %s -> ( ( 2 x. T ) / %s ) = ( 2 / %s ) )' % (A0, G, TL))],
           'eqtrd', '( %s -> ( ( 1 / %s ) x. ( 2 x. T ) ) = ( 2 / %s ) )' % (A0, G, TL))
# 2 / ( T L ) <_ ( 2 U^C ) / ( T L )  since 1 <_ U^C
uc1 = w.s([w.s([w.s([d['ur'], w.s([a1(w, A0, '1re', '1 e. RR'), d['ur'], d['u1']], 'ltled', '( %s -> 1 <_ U )' % A0)], 'jca', '( %s -> ( U e. RR /\\ 1 <_ U ) )' % A0),
                w.s([a1(w, A0, '0re', '0 e. RR'), cl.mem('C', 'RR')], 'jca', '( %s -> ( 0 e. RR /\\ C e. RR ) )' % A0),
                w.s([d['crp']], 'rpge0d', '( %s -> 0 <_ C )' % A0)], '3jca', '( %s -> ( ( U e. RR /\\ 1 <_ U ) /\\ ( 0 e. RR /\\ C e. RR ) /\\ 0 <_ C ) )' % A0), w.inst('cxplea')], 'syl',
          '( %s -> ( U ^c 0 ) <_ %s )' % (A0, UC))
uc1b = w.s([w.s([w.s([uc, w.inst('cxp0')], 'syl', '( %s -> ( U ^c 0 ) = 1 )' % A0)], 'eqcomd', '( %s -> 1 = ( U ^c 0 ) )' % A0), uc1], 'eqbrtrd', '( %s -> 1 <_ %s )' % (A0, UC))
two = linarith(w, A0, [uc1b], '2 <_ ( 2 x. %s )' % UC, closure=cl)
c1 = w.s([a1(w, A0, '2re', '2 e. RR'), cl.mem('( 2 x. %s )' % UC, 'RR'), d['tlrp'], two], 'lediv1dd', '( %s -> ( 2 / %s ) <_ %s )' % (A0, TL, BND1))
fin1 = w.s([cl.mem('( ( %s / %s ) x. ( 2 x. T ) )' % (UNF, FA), 'RR'), cl.mem('( ( 1 / %s ) x. ( 2 x. T ) )' % G, 'RR'), d['bndr'], s4,
            w.s([balg, c1], 'eqbrtrd', '( %s -> ( ( 1 / %s ) x. ( 2 x. T ) ) <_ %s )' % (A0, G, BND1))], 'letrd',
           '( %s -> ( ( %s / %s ) x. ( 2 x. T ) ) <_ %s )' % (A0, UNF, FA, BND1))
fcn = pkfcn_(w, A0, d['urp'])
ss = segv(w, A0, NFA, 'T', '-u T', d['nfar'], d['nfane'], tr, ntr)
pac = cptcl(w, A0, NFA, 'T', d['nfar'], tr); pbc = cptcl(w, A0, NFA, '-u T', d['nfar'], ntr)
ecl, _ = edgecl(w, A0, PA, PB, pac, pbc, fcn, ss)
vbr = w.s([vbeq, cl.mem('( ( %s / %s ) x. ( 2 x. T ) )' % (UNF, FA), 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, VB))
w.qed([w.s([ecl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E(PA, PB))), vbr, d['bndr'], v1, w.s([vbeq, fin1], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, VB, BND1))],
      'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E(PA, PB), BND1))
run7(w)

# ---------------------------------------------------------------- pkgt1
A0 = B0
w = W('pkgt1', 'The far-regime bound on the truncated Perron kernel for ` 1 < U `: the kernel '
      'line differs from ` 2 _i _pi ` by at most ` 6 U ^c C / ( T log U ) `.  The contour is '
      'shifted left past the pole to the far abscissa ( ~ pkrecidc , ~ farabs ) and the three '
      'far edges are bounded ( ~ pkgt1h , ~ pkgt1v , ~ edgesol ).  This is '
      '` norm_perronKernel_sub_one_le ` of Route Z\'s PerronKernel.lean, times ` 2 _pi `.')
d = gt1ctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
cl = d['cl']
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR'); cr = cl.mem('C', 'RR')
t0 = cl.gt0('T'); nt0 = linarith(w, A0, [t0], '-u T < 0', closure=cl)
E1 = E(CPT(NFA, '-u T'), CPT('C', '-u T')); E2 = PK; E3 = E(CPT('C', 'T'), CPT(NFA, 'T')); E4 = E(CPT(NFA, 'T'), CPT(NFA, '-u T'))
rid = w.s([d['urp'], w.s([w.s([d['nfar'], cr], 'jca', '( %s -> ( %s e. RR /\\ C e. RR ) )' % (A0, NFA)), w.s([ntr, tr], 'jca', '( %s -> ( -u T e. RR /\\ T e. RR ) )' % A0)], 'jca',
                          '( %s -> ( ( %s e. RR /\\ C e. RR ) /\\ ( -u T e. RR /\\ T e. RR ) ) )' % (A0, NFA)),
           w.s([w.s([d['nfa0'], cl.gt0('C')], 'jca', '( %s -> ( %s < 0 /\\ 0 < C ) )' % (A0, NFA)), w.s([nt0, t0], 'jca', '( %s -> ( -u T < 0 /\\ 0 < T ) )' % A0)], 'jca',
               '( %s -> ( ( %s < 0 /\\ 0 < C ) /\\ ( -u T < 0 /\\ 0 < T ) ) )' % (A0, NFA)), w.inst('pkrecidc')], 'syl3anc',
          '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = %s )' % (A0, E1, E2, E3, E4, TPI))
# closures of the four edges
fcn = pkfcn_(w, A0, d['urp'])
nsne = w.s([nt0], 'lt0ne0d', '( %s -> -u T =/= 0 )' % A0); tne = w.s([d['trp']], 'rpne0d', '( %s -> T =/= 0 )' % A0)
p1 = cptcl(w, A0, NFA, '-u T', d['nfar'], ntr); p2 = cptcl(w, A0, 'C', '-u T', cr, ntr); p3 = cptcl(w, A0, 'C', 'T', cr, tr); p4 = cptcl(w, A0, NFA, 'T', d['nfar'], tr)
e1c, _ = edgecl(w, A0, CPT(NFA, '-u T'), CPT('C', '-u T'), p1, p2, fcn, segh(w, A0, '-u T', NFA, 'C', ntr, nsne, d['nfar'], cr))
e2c = w.s([d['urp'], d['crp'], d['trp'], w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (A0, E2))
ss3 = segh(w, A0, 'T', NFA, 'C', tr, tne, d['nfar'], cr)
ss3r = w.s([w.s([w.s([p3, p4], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CPT('C', 'T'), CPT(NFA, 'T'))), w.inst('csegcom')], 'syl',
                '( %s -> ( %s cseg %s ) = ( %s cseg %s ) )' % (A0, CPT('C', 'T'), CPT(NFA, 'T'), CPT(NFA, 'T'), CPT('C', 'T'))), ss3], 'eqsstrd',
           '( %s -> ( %s cseg %s ) C_ %s )' % (A0, CPT('C', 'T'), CPT(NFA, 'T'), DOM))
e3c, _ = edgecl(w, A0, CPT('C', 'T'), CPT(NFA, 'T'), p3, p4, fcn, ss3r)
e4c, _ = edgecl(w, A0, CPT(NFA, 'T'), CPT(NFA, '-u T'), p4, p1, fcn, segv(w, A0, NFA, 'T', '-u T', d['nfar'], d['nfane'], tr, ntr))
tpic = w.s([a1(w, A0, '2cn', '2 e. CC'), w.s([a1(w, A0, 'ax-icn', '_i e. CC'), w.s([a1(w, A0, 'pire', '_pi e. RR')], 'recnd', '( %s -> _pi e. CC )' % A0)], 'mulcld',
                                                '( %s -> ( _i x. _pi ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, TPI))
com = w.s([w.s([e1c, e2c], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, E1, E2)), w.s([e3c, e4c], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, E3, E4))], 'addcomd',
          '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, E1, E2, E3, E4, E3, E4, E1, E2))
rid2 = w.s([w.s([com], 'eqcomd', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, E3, E4, E1, E2, E1, E2, E3, E4)), rid], 'eqtrd',
           '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = %s )' % (A0, E3, E4, E1, E2, TPI))
sol = w.s([w.s([w.s([w.s([e3c, e4c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, E3, E4)), w.s([e1c, e2c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, E1, E2))], 'jca',
                     '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, E3, E4, E1, E2)), tpic], 'jca',
                '( %s -> ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) /\\ %s e. CC ) )' % (A0, E3, E4, E1, E2, TPI)), w.inst('edgesol')], 'syl',
          '( %s -> ( ( ( %s + %s ) + ( %s + %s ) ) = %s -> ( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) ) )' % (A0, E3, E4, E1, E2, TPI, E2, TPI, E3, E4, E1))
tri = w.s([rid2, sol], 'mpd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A0, E2, TPI, E3, E4, E1))
# the three edge bounds
abst = w.s([tr, w.s([d['trp']], 'rpge0d', '( %s -> 0 <_ T )' % A0)], 'absidd', '( %s -> ( abs ` T ) = T )' % A0)
absnt = w.s([w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'absnegd', '( %s -> ( abs ` -u T ) = ( abs ` T ) )' % A0), abst], 'eqtrd', '( %s -> ( abs ` -u T ) = T )' % A0)
hT = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([tr, abst], 'jca', '( %s -> ( T e. RR /\\ ( abs ` T ) = T ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( T e. RR /\\ ( abs ` T ) = T ) ) )' % (A0, B0)),
          w.inst('pkgt1h')], 'syl', '( %s -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (A0, E(CPT(NFA, 'T'), CPT('C', 'T')), BND1, E3, BND1))
hnT = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([ntr, absnt], 'jca', '( %s -> ( -u T e. RR /\\ ( abs ` -u T ) = T ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( -u T e. RR /\\ ( abs ` -u T ) = T ) ) )' % (A0, B0)),
           w.inst('pkgt1h')], 'syl', '( %s -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (A0, E1, BND1, E(CPT('C', '-u T'), CPT(NFA, '-u T')), BND1))
b3 = w.s([hT, w.inst('simpr')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E3, BND1))
b1 = w.s([hnT, w.inst('simpl')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E1, BND1))
b4 = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('pkgt1v')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, E4, BND1))
a3 = w.s([e3c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E3)); a4 = w.s([e4c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E4)); a1e = w.s([e1c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, E1))
cl.atom(BND1); cl.have(BND1, 'RR', d['bndr'])
for X, st in ((E3, a3), (E4, a4), (E1, a1e)):
    cl.atom('( abs ` %s )' % X); cl.have('( abs ` %s )' % X, 'RR', st)
s6 = linarith(w, A0, [b3, b4, b1], '( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) <_ ( 3 x. %s )' % (E3, E4, E1, BND1), closure=cl)
# 3 x. BND1 = ( 6 U^C ) / ( T L )
uc2c = w.s([cl.mem('( 2 x. %s )' % UC, 'RR')], 'recnd', '( %s -> ( 2 x. %s ) e. CC )' % (A0, UC))
tlc = w.s([d['tlrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, TL)); tlne = w.s([d['tlrp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, TL))
ucc = w.s([d['ucrp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, UC))
m1 = w.s([w.s([a1(w, A0, '3cn', '3 e. CC'), uc2c, tlc, tlne], 'divassd', '( %s -> ( ( 3 x. ( 2 x. %s ) ) / %s ) = ( 3 x. %s ) )' % (A0, UC, TL, BND1))], 'eqcomd',
         '( %s -> ( 3 x. %s ) = ( ( 3 x. ( 2 x. %s ) ) / %s ) )' % (A0, BND1, UC, TL))
m2 = w.s([w.s([w.s([a1(w, A0, '3cn', '3 e. CC'), a1(w, A0, '2cn', '2 e. CC'), ucc], 'mulassd', '( %s -> ( ( 3 x. 2 ) x. %s ) = ( 3 x. ( 2 x. %s ) ) )' % (A0, UC, UC))], 'eqcomd',
               '( %s -> ( 3 x. ( 2 x. %s ) ) = ( ( 3 x. 2 ) x. %s ) )' % (A0, UC, UC)),
          w.s([a1(w, A0, '3t2e6', '( 3 x. 2 ) = 6')], 'oveq1d', '( %s -> ( ( 3 x. 2 ) x. %s ) = ( 6 x. %s ) )' % (A0, UC, UC))], 'eqtrd', '( %s -> ( 3 x. ( 2 x. %s ) ) = ( 6 x. %s ) )' % (A0, UC, UC))
m3 = w.s([m1, w.s([m2], 'oveq1d', '( %s -> ( ( 3 x. ( 2 x. %s ) ) / %s ) = ( ( 6 x. %s ) / %s ) )' % (A0, UC, TL, UC, TL))], 'eqtrd', '( %s -> ( 3 x. %s ) = ( ( 6 x. %s ) / %s ) )' % (A0, BND1, UC, TL))
sumr = cl.mem('( ( abs ` %s ) + ( ( abs ` %s ) + ( abs ` %s ) ) )' % (E3, E4, E1), 'RR')
fin = w.s([w.s([w.s([e2c, tpic], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, E2, TPI))], 'abscld', '( %s -> ( abs ` ( %s - %s ) ) e. RR )' % (A0, E2, TPI)), sumr, cl.mem('( 3 x. %s )' % BND1, 'RR'), tri, s6],
          'letrd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( 3 x. %s ) )' % (A0, E2, TPI, BND1))
w.qed([fin, m3], 'breqtrd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( ( 6 x. %s ) / %s ) )' % (A0, E2, TPI, UC, TL))
run7(w)
