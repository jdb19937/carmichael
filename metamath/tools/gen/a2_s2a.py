"""Sortie A2, batch 3: the scale inequalities of Step2W (log z <_ 2 ell3,
z ^ ( 99 / 100 ) <_ ell2)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

L2 = '( ell2 ` N )'; L3 = '( ell3 ` N )'
ZR = '( ( C x. %s ) x. %s )' % (L2, L3)
PB = '( ( 4 x. C ) x. %s )' % L3
Q99 = '( ; 9 9 / ; ; 1 0 0 )'


def ctx(w):
    """the common hypotheses; returns a dict of steps"""
    d = {}
    d['cr'] = w.h('C e. RR')
    d['c1'] = w.h('1 <_ C')
    d['n3'] = w.h('N e. ( ZZ>= ` 3 )')
    d['b16'] = w.h('( ; 1 6 x. C ) <_ %s' % L3)
    d['a1'] = w.h('1 <_ %s' % L2)
    return d


def basics(w, d, A='ph'):
    d['n2'] = w.s([d['n3'], w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
    d['ar'] = w.s([d['n2'], w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, L2))
    d['br'] = w.s([d['n3'], w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, L3))
    d['n0'] = w.s([w.s([d['n2'], w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % A)], 'nnnn0d', '( %s -> N e. NN0 )' % A)
    lv = {'C': d['cr'], L2: d['ar'], L3: d['br']}
    d['b16v'] = linarith(w, A, [d['b16'], d['c1']], '; 1 6 <_ %s' % L3, leaves=lv)
    d['b0'] = linarith(w, A, [d['b16'], d['c1']], '0 < %s' % L3, leaves=lv)
    d['bge0'] = w.s([d['b0']], 'ltled', '( %s -> 0 <_ %s )' % (A, L3))
    d['brp'] = w.s([d['br'], d['b0']], 'elrpd', '( %s -> %s e. RR+ )' % (A, L3))
    d['a0'] = linarith(w, A, [d['a1']], '0 < %s' % L2, leaves=lv)
    d['age0'] = w.s([d['a0']], 'ltled', '( %s -> 0 <_ %s )' % (A, L2))
    d['arp'] = w.s([d['ar'], d['a0']], 'elrpd', '( %s -> %s e. RR+ )' % (A, L2))
    d['c4'] = w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % A)
    d['fcr'] = w.s([d['c4'], d['cr']], 'remulcld', '( %s -> ( 4 x. C ) e. RR )' % A)
    d['pbr'] = w.s([d['fcr'], d['br']], 'remulcld', '( %s -> %s e. RR )' % (A, PB))
    d['pblv'] = dict(lv); d['pblv'][PB] = d['pbr']
    # 4 C <_ ell3 N and 1 <_ 4 C
    d['fcb'] = linarith(w, A, [d['b16'], d['c1']], '( 4 x. C ) <_ %s' % L3, leaves=lv)
    d['fc1'] = linarith(w, A, [d['c1']], '1 <_ ( 4 x. C )', leaves=lv)
    d['fc0'] = linarith(w, A, [d['c1']], '0 <_ ( 4 x. C )', leaves=lv)
    # 1 <_ PB
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    l12 = w.s([one, d['fcr'], one, d['br'],
               w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A),
               w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A),
               d['fc1'],
               linarith(w, A, [d['b16'], d['c1']], '1 <_ %s' % L3, leaves=lv)],
              'lemul12ad', '( %s -> ( 1 x. 1 ) <_ %s )' % (A, PB))
    t11 = w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % A)
    d['pb1'] = w.s([w.s([t11], 'eqcomd', '( %s -> 1 = ( 1 x. 1 ) )' % A), l12], 'eqbrtrd', '( %s -> 1 <_ %s )' % (A, PB))
    d['pb0'] = linarith(w, A, [d['pb1']], '0 < %s' % PB, leaves=d['pblv'])
    d['pbrp'] = w.s([d['pbr'], d['pb0']], 'elrpd', '( %s -> %s e. RR+ )' % (A, PB))
    # Z <_ 4 ( C A B ) = A x. PB
    d['zc'] = w.s([w.s([], '4cn', '4 e. CC')], 'a1i', '( %s -> 4 e. CC )' % A)
    rot = w.s([w.s([d['zc'], w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A)], 'jca',
                   '( %s -> ( 4 e. CC /\\ C e. CC ) )' % A),
               w.s([w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A, L2)),
                    w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A, L3))], 'jca',
                   '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A, L2, L3)),
               w.inst('mul4rot')], 'syl2anc',
              '( %s -> ( 4 x. %s ) = ( %s x. %s ) )' % (A, ZR, L2, PB))
    d['rot'] = rot
    return d


# ------------------------------------------------------------------ s2logz
w = WH('s2logz', 'Step 2 at windowed scales: log z <_ 2 ell3 n (Lean: Step2W.lean hlogz).')
d = ctx(w)
zn = w.h('Z e. NN')
zhi = w.h('Z <_ ( 4 x. %s )' % ZR)
basics(w, d)
A = 'ph'
# PB <_ ( ell3 N ) ^ 2
mul = w.s([d['fcr'], d['br'], d['br'], d['bge0'], d['fcb']], 'lemul1ad',
          '( %s -> %s <_ ( %s x. %s ) )' % (A, PB, L3, L3))
sv = w.s([w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A, L3))], 'sqvald',
         '( %s -> ( %s ^ 2 ) = ( %s x. %s ) )' % (A, L3, L3, L3))
sqr = w.s([d['br']], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A, L3))
pbsq = w.s([mul, w.s([sv], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s ^ 2 ) )' % (A, L3, L3, L3))], 'breqtrd',
           '( %s -> %s <_ ( %s ^ 2 ) )' % (A, PB, L3))
lv2 = dict(d['pblv']); lv2['( %s ^ 2 )' % L3] = sqr
m1le = linarith(w, A, [pbsq], '( %s - 1 ) <_ ( %s ^ 2 )' % (PB, L3), leaves=lv2)
m10 = linarith(w, A, [d['pb1']], '0 <_ ( %s - 1 )' % PB, leaves=d['pblv'])
one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
pbm1 = w.s([d['pbr'], one], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (A, PB))
ls = w.s([pbm1, m10, w.inst('loglesqrt')], 'syl2anc',
         '( %s -> ( log ` ( ( %s - 1 ) + 1 ) ) <_ ( sqrt ` ( %s - 1 ) ) )' % (A, PB, PB))
npc = w.s([w.s([d['pbr']], 'recnd', '( %s -> %s e. CC )' % (A, PB)),
           w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A)], 'npcand',
          '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (A, PB, PB))
ls2 = w.s([w.s([npc], 'fveq2d', '( %s -> ( log ` ( ( %s - 1 ) + 1 ) ) = ( log ` %s ) )' % (A, PB, PB))], 'eqcomd',
          '( %s -> ( log ` %s ) = ( log ` ( ( %s - 1 ) + 1 ) ) )' % (A, PB, PB))
ls3 = w.s([ls2, ls], 'eqbrtrd', '( %s -> ( log ` %s ) <_ ( sqrt ` ( %s - 1 ) ) )' % (A, PB, PB))
sq = sqrtle2(w, A, '( %s - 1 )' % PB, L3, pbm1, m10, d['br'], d['bge0'], m1le)
sqrr = w.s([pbm1, m10, w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` ( %s - 1 ) ) e. RR )' % (A, PB))
lpbr = w.s([d['pbrp'], w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (A, PB))
lpb = w.s([lpbr, sqrr, d['br'], ls3, sq], 'letrd', '( %s -> ( log ` %s ) <_ %s )' % (A, PB, L3))
# log Z <_ log ( A x. PB ) = log A + log PB
zrp = w.s([zn], 'nnrpd', '( %s -> Z e. RR+ )' % A)
apbrp = w.s([d['arp'], d['pbrp']], 'rpmulcld', '( %s -> ( %s x. %s ) e. RR+ )' % (A, L2, PB))
zle = w.s([zhi, d['rot']], 'breqtrd', '( %s -> Z <_ ( %s x. %s ) )' % (A, L2, PB))
bi = w.s([zrp, apbrp, w.inst('logleb')], 'syl2anc',
         '( %s -> ( Z <_ ( %s x. %s ) <-> ( log ` Z ) <_ ( log ` ( %s x. %s ) ) ) )' % (A, L2, PB, L2, PB))
lz = w.s([zle, bi], 'mpbid', '( %s -> ( log ` Z ) <_ ( log ` ( %s x. %s ) ) )' % (A, L2, PB))
lm = w.s([d['arp'], d['pbrp'], w.inst('relogmul')], 'syl2anc',
         '( %s -> ( log ` ( %s x. %s ) ) = ( ( log ` %s ) + ( log ` %s ) ) )' % (A, L2, PB, L2, PB))
lz2 = w.s([lz, lm], 'breqtrd', '( %s -> ( log ` Z ) <_ ( ( log ` %s ) + ( log ` %s ) ) )' % (A, L2, PB))
iv = w.s([d['n0'], w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, L3, L2))
lz3 = w.s([w.s([iv], 'oveq1d', '( %s -> ( %s + ( log ` %s ) ) = ( ( log ` %s ) + ( log ` %s ) ) )' % (A, L3, PB, L2, PB))], 'eqcomd',
          '( %s -> ( ( log ` %s ) + ( log ` %s ) ) = ( %s + ( log ` %s ) ) )' % (A, L2, PB, L3, PB))
lz4 = w.s([lz2, lz3], 'breqtrd', '( %s -> ( log ` Z ) <_ ( %s + ( log ` %s ) ) )' % (A, L3, PB))
lzr = w.s([zrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` Z ) e. RR )' % A)
lvz = {L3: d['br'], '( log ` %s )' % PB: lpbr, '( log ` Z )': lzr}
linarith(w, A, [lz4, lpb], '( log ` Z ) <_ ( 2 x. %s )' % L3, leaves=lvz, name='qed')
run(w)

# ------------------------------------------------------------------ s2rpz
Q100 = '( ; ; 1 0 0 / ; 9 9 )'
E99 = '( 1 / ; 9 9 )'
AE = '( %s ^c %s )' % (L2, E99)
w = WH('s2rpz', 'Step 2 at windowed scales: z ^ ( 99 / 100 ) <_ ell2 n (Lean: Step2W.lean hrpz).')
d = ctx(w)
hyp99 = w.h('%s <_ %s' % (PB, AE))
zn0 = w.h('Z e. NN0')
zhi = w.h('Z <_ ( 4 x. %s )' % ZR)
basics(w, d)
A = 'ph'
e99r = w.s([num.fact(w, E99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, E99))
aer = w.s([d['ar'], d['age0'], e99r], 'recxpcld', '( %s -> %s e. RR )' % (A, AE))
mul = w.s([d['pbr'], aer, d['ar'], d['age0'], hyp99], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, L2, PB, L2, AE))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
zge0 = w.s([zn0], 'nn0ge0d', '( %s -> 0 <_ Z )' % A)
zle = w.s([zhi, d['rot']], 'breqtrd', '( %s -> Z <_ ( %s x. %s ) )' % (A, L2, PB))
apb = w.s([d['ar'], d['pbr']], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A, L2, PB))
aae = w.s([d['ar'], aer], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A, L2, AE))
zle2 = w.s([zr, apb, aae, zle, mul], 'letrd', '( %s -> Z <_ ( %s x. %s ) )' % (A, L2, AE))
# ( ell2 N ) ^c ( 100 / 99 ) = ell2 N x. ( ell2 N ) ^c ( 1 / 99 )
acn = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A, L2))
ane = w.s([d['arp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A, L2))
onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % A)
e99c = w.s([e99r], 'recnd', '( %s -> %s e. CC )' % (A, E99))
ca = w.s([w.s([acn, ane], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A, L2, L2)), onec, e99c, w.inst('cxpadd')], 'syl3anc',
         '( %s -> ( %s ^c ( 1 + %s ) ) = ( ( %s ^c 1 ) x. %s ) )' % (A, L2, E99, L2, AE))
c1e = w.s([acn], 'cxp1d', '( %s -> ( %s ^c 1 ) = %s )' % (A, L2, L2))
ca2 = w.s([ca, w.s([c1e], 'oveq1d', '( %s -> ( ( %s ^c 1 ) x. %s ) = ( %s x. %s ) )' % (A, L2, AE, L2, AE))], 'eqtrd',
          '( %s -> ( %s ^c ( 1 + %s ) ) = ( %s x. %s ) )' % (A, L2, E99, L2, AE))
pe = w.s([w.s([], 'p10099', '( 1 + %s ) = %s' % (E99, Q100))], 'a1i', '( %s -> ( 1 + %s ) = %s )' % (A, E99, Q100))
ca3 = w.s([w.s([w.s([pe], 'oveq2d', '( %s -> ( %s ^c ( 1 + %s ) ) = ( %s ^c %s ) )' % (A, L2, E99, L2, Q100))], 'eqcomd',
               '( %s -> ( %s ^c %s ) = ( %s ^c ( 1 + %s ) ) )' % (A, L2, Q100, L2, E99)), ca2], 'eqtrd',
          '( %s -> ( %s ^c %s ) = ( %s x. %s ) )' % (A, L2, Q100, L2, AE))
zle3 = w.s([zle2, w.s([ca3], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s ^c %s ) )' % (A, L2, AE, L2, Q100))], 'breqtrd',
           '( %s -> Z <_ ( %s ^c %s ) )' % (A, L2, Q100))
q99r = w.s([num.fact(w, Q99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, Q99))
q990 = w.s([num.fact(w, Q99, 'ge0')], 'a1i', '( %s -> 0 <_ %s )' % (A, Q99))
q100r = w.s([num.fact(w, Q100, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, Q100))
aq100 = w.s([d['ar'], d['age0'], q100r], 'recxpcld', '( %s -> ( %s ^c %s ) e. RR )' % (A, L2, Q100))
cx = w.s([zr, aq100, q99r, zge0, q990, zle3], 'cxple2ad', '( %s -> ( Z ^c %s ) <_ ( ( %s ^c %s ) ^c %s ) )' % (A, Q99, L2, Q100, Q99))
q99c = w.s([q99r], 'recnd', '( %s -> %s e. CC )' % (A, Q99))
cm = w.s([d['arp'], q100r, q99c, w.inst('cxpmul')], 'syl3anc',
         '( %s -> ( %s ^c ( %s x. %s ) ) = ( ( %s ^c %s ) ^c %s ) )' % (A, L2, Q100, Q99, L2, Q100, Q99))
qq = w.s([w.s([], 'q9910', '( %s x. %s ) = 1' % (Q100, Q99))], 'a1i', '( %s -> ( %s x. %s ) = 1 )' % (A, Q100, Q99))
cm2 = w.s([w.s([qq], 'oveq2d', '( %s -> ( %s ^c ( %s x. %s ) ) = ( %s ^c 1 ) )' % (A, L2, Q100, Q99, L2)), c1e], 'eqtrd',
          '( %s -> ( %s ^c ( %s x. %s ) ) = %s )' % (A, L2, Q100, Q99, L2))
fin = w.s([w.s([cm], 'eqcomd', '( %s -> ( ( %s ^c %s ) ^c %s ) = ( %s ^c ( %s x. %s ) ) )' % (A, L2, Q100, Q99, L2, Q100, Q99)), cm2], 'eqtrd',
          '( %s -> ( ( %s ^c %s ) ^c %s ) = %s )' % (A, L2, Q100, Q99, L2))
w.qed([cx, fin], 'breqtrd', '( %s -> ( Z ^c %s ) <_ %s )' % (A, Q99, L2))
run(w)
