"""Sortie A5, batch 5: step 3 of the assembly, the shift and the pool list
(Lean: SearchAlg.lean lines 141-170).
MM_DB=sorties/a5.mm python3 tools/gen/a5_k.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from tm import *
from a2lib import WH
from lin import linarith
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

PRD = 'prod_ i e. ( 0 ..^ ( # ` Q ) ) ( Q ` i )'
X5 = '( A ^ 5 )'
P5 = '( %s ^ 5 )' % PRD
PLA = '( 1st ` ( ( ( Q PoolAlg %s ) ` Z ) ` K ) )' % X5
PLP = '( 1st ` ( ( ( Q PoolAlg %s ) ` Z ) ` K ) )' % P5
POOL = '( ( ran Q pool Z ) ` K )'

# --------------------------------------------------------------- a5pay
w = WH('a5pay', 'The payload of a successful Option result is a pair of a number and a word (Lean: the some (k, P) and some (m, S) patterns).')
h1 = w.h('D e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )')
h2 = w.h('( 1st ` D ) =/= ( inr ` (/) )')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
d1 = st([h1, w.inst('xp1st')], 'syl', '( 1st ` D ) e. ( ( NN0 X. Word NN0 ) |_| 1o )')
dj = st([st([d1, h2], 'jca', '( ( 1st ` D ) e. ( ( NN0 X. Word NN0 ) |_| 1o ) /\\ ( 1st ` D ) =/= ( inr ` (/) ) )'),
         w.inst('algdjun')], 'syl',
        '( ( 2nd ` ( 1st ` D ) ) e. ( NN0 X. Word NN0 ) /\\ ( 1st ` D ) = ( inl ` ( 2nd ` ( 1st ` D ) ) ) )')
pr = st([dj], 'simpld', '( 2nd ` ( 1st ` D ) ) e. ( NN0 X. Word NN0 )')
w.qed([st([pr, w.inst('xp1st')], 'syl', '( 1st ` ( 2nd ` ( 1st ` D ) ) ) e. NN0'),
       st([pr, w.inst('xp2nd')], 'syl', '( 2nd ` ( 2nd ` ( 1st ` D ) ) ) e. Word NN0')], 'jca',
      '( ph -> ( ( 1st ` ( 2nd ` ( 1st ` D ) ) ) e. NN0 /\\ ( 2nd ` ( 2nd ` ( 1st ` D ) ) ) e. Word NN0 ) )')
run(w)

# --------------------------------------------------------------- a5kf
w = WH('a5kf', 'The accepted shift of step 3 is below the fuel of the scan (Lean: hk0fuel of SearchAlg.lean).')
h1 = w.h('A e. NN')
h2 = w.h('K e. NN')
h3 = w.h('K <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) )' % X5)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
a5n = st([h1, w.s([num.fact(w, '5', 'NN0')], 'a1i', '( ph -> 5 e. NN0 )'), w.inst('nnexpcl')], 'syl2anc',
         '%s e. NN' % X5)
a5r = st([a5n], 'nnred', '%s e. RR' % X5)
a5g = st([a5n], 'nnge1d', '1 <_ %s' % X5)
er = w.s([num.fact(w, '( ; 7 9 / ; ; 1 0 0 )', 'RR')], 'a1i', '( ph -> ( ; 7 9 / ; ; 1 0 0 ) e. RR )')
o1 = w.s([num.fact(w, '1', 'RR')], 'a1i', '( ph -> 1 e. RR )')
e0 = w.s([num.fact(w, '( ; 7 9 / ; ; 1 0 0 )', 'ge0')], 'a1i', '( ph -> 0 <_ ( ; 7 9 / ; ; 1 0 0 ) )')
ele = linarith(w, 'ph', [e0], '( ; 7 9 / ; ; 1 0 0 ) <_ 1')
mono = w.s([a5r, a5g, er, o1, ele], 'cxplead',
           '( ph -> ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) <_ ( %s ^c 1 ) )' % (X5, X5))
c1 = w.s([st([a5r], 'recnd', '%s e. CC' % X5)], 'cxp1d', '( ph -> ( %s ^c 1 ) = %s )' % (X5, X5))
a50 = st([st([a5n], 'nnnn0d', '%s e. NN0' % X5)], 'nn0ge0d', '0 <_ %s' % X5)
midre = st([a5r, a50, er], 'recxpcld', '( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) e. RR' % X5)
kre = st([h2], 'nnred', 'K e. RR')
w.qed([kre, midre, a5r, h3, st([mono, c1], 'breqtrd', '( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) <_ %s' % (X5, X5))],
      'letrd', '( ph -> K <_ %s )' % X5)
run(w)

# --------------------------------------------------------------- a5kc
w = WH('a5kc', 'The coprimality test of the scan agrees with coprimality to the modulus (Lean: coprimeTo_spec at Lmod).')
h1 = w.h('( Q e. Word NN0 /\\ A. q e. ran Q q e. Prime )')
h2 = w.h('K e. NN')
h3 = w.h('A = %s' % PRD)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
qcl = st([h1], 'simpld', 'Q e. Word NN0')
qp = st([h1], 'simprd', 'A. q e. ran Q q e. Prime')
spec = st([st([st([qcl, h2], 'jca', '( Q e. Word NN0 /\\ K e. NN )'), qp], 'jca',
              '( ( Q e. Word NN0 /\\ K e. NN ) /\\ A. q e. ran Q q e. Prime )'),
           w.inst('coprimetospec')], 'syl',
          '( ( 1st ` ( Q CoprimeTo K ) ) = 1o <-> ( K gcd %s ) = 1 )' % PRD)
ov = w.s([st([h3], 'eqcomd', '%s = A' % PRD)], 'oveq2d',
         '( ph -> ( K gcd %s ) = ( K gcd A ) )' % PRD)
eq = w.s([ov], 'eqeq1d', '( ph -> ( ( K gcd %s ) = 1 <-> ( K gcd A ) = 1 ) )' % PRD)
w.qed([spec, eq], 'bitrd', '( ph -> ( ( 1st ` ( Q CoprimeTo K ) ) = 1o <-> ( K gcd A ) = 1 ) )')
run(w)

# --------------------------------------------------------------- a5kp
w = WH('a5kp', 'The pool list of the algorithm enumerates the pool of the paper (Lean: poolAlg_spec at the exact ceiling).')
h1 = w.h('( Q e. Word NN0 /\\ Fun `\' Q /\\ A. q e. ran Q q e. Prime )')
h2 = w.h('( Z e. NN0 /\\ K e. NN0 )')
h3 = w.h('A = %s' % PRD)
h4 = w.h('%s e. NN0' % X5)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
qcl = st([h1], 'simp1d', 'Q e. Word NN0')
qfun = st([h1], 'simp2d', 'Fun `\' Q')
zn0 = st([h2], 'simpld', 'Z e. NN0')
kn0 = st([h2], 'simprd', 'K e. NN0')
# ( A ^ 5 ) = ( PRD ^ 5 ), hence the two PoolAlg terms agree
pe = w.s([h3], 'oveq1d', '( ph -> %s = %s )' % (X5, P5))
pa = w.s([w.s([pe], 'oveq2d', '( ph -> ( Q PoolAlg %s ) = ( Q PoolAlg %s ) )' % (X5, P5))], 'fveq1d',
         '( ph -> ( ( Q PoolAlg %s ) ` Z ) = ( ( Q PoolAlg %s ) ` Z ) )' % (X5, P5))
pb = w.s([pa], 'fveq1d', '( ph -> ( ( ( Q PoolAlg %s ) ` Z ) ` K ) = ( ( ( Q PoolAlg %s ) ` Z ) ` K ) )' % (X5, P5))
pc = w.s([pb], 'fveq2d', '( ph -> %s = %s )' % (PLA, PLP))
spec = st([st([h1, h2], 'jca',
              '( ( Q e. Word NN0 /\\ Fun `\' Q /\\ A. q e. ran Q q e. Prime ) /\\ ( Z e. NN0 /\\ K e. NN0 ) )'),
           w.inst('poolalgspec')], 'syl',
          '( Fun `\' %s /\\ ran %s = %s )' % (PLP, PLP, POOL))
pfun = st([st([spec], 'simpld', 'Fun `\' %s' % PLP),
           w.s([w.s([pc], 'cnveqd', '( ph -> `\' %s = `\' %s )' % (PLA, PLP))], 'funeqd',
               '( ph -> ( Fun `\' %s <-> Fun `\' %s ) )' % (PLA, PLP))], 'mpbird', 'Fun `\' %s' % PLA)
prn = st([w.s([pc], 'rneqd', '( ph -> ran %s = ran %s )' % (PLA, PLP)),
          st([spec], 'simprd', 'ran %s = %s' % (PLP, POOL))], 'eqtrd', 'ran %s = %s' % (PLA, POOL))
pcl = st([st([st([st([qcl, h4], 'jca', '( Q e. Word NN0 /\\ %s e. NN0 )' % X5), zn0], 'jca',
              '( ( Q e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 )' % X5), kn0], 'jca',
             '( ( ( Q e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 ) /\\ K e. NN0 )' % X5),
          w.inst('poolalgcl')], 'syl', '( ( ( Q PoolAlg %s ) ` Z ) ` K ) e. ( Word NN0 X. NN0 )' % X5)
pw = st([pcl, w.inst('xp1st')], 'syl', '%s e. Word NN0' % PLA)
pcard = st([st([st([pw, pfun], 'jca', '( %s e. Word NN0 /\\ Fun `\' %s )' % (PLA, PLA)),
               w.inst('algwrdcard')], 'syl', '( # ` ran %s ) = ( # ` %s )' % (PLA, PLA)),
            w.s([prn], 'fveq2d', '( ph -> ( # ` ran %s ) = ( # ` %s ) )' % (PLA, POOL))], 'eqtr3d',
           '( # ` %s ) = ( # ` %s )' % (PLA, POOL))
w.qed([st([pw, pfun], 'jca', '( %s e. Word NN0 /\\ Fun `\' %s )' % (PLA, PLA)),
       st([prn, pcard], 'jca', '( ran %s = %s /\\ ( # ` %s ) = ( # ` %s ) )' % (PLA, POOL, PLA, POOL))], 'jca',
      '( ph -> ( ( %s e. Word NN0 /\\ Fun `\' %s ) /\\ ( ran %s = %s /\\ ( # ` %s ) = ( # ` %s ) ) ) )'
      % (PLA, PLA, PLA, POOL, PLA, POOL))
run(w)

# --------------------------------------------------------------- a5ks
SCN = '( ( ( ( ( Q Scan %s ) ` Z ) ` H ) ` 1 ) ` %s )' % (X5, X5)
KS = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % SCN
PS = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % SCN
KJ = '( 1st ` ( 2nd ` ( 1st ` J ) ) )'
PJ = '( 2nd ` ( 2nd ` ( 1st ` J ) ) )'
CB = '( ( ( # ` Q ) + 2 ) + ( ( 2 ^ ( # ` Q ) ) x. ( ( Nfloor ` ( sqrt ` %s ) ) + 3 ) ) )' % X5
PGA = lambda k: '( 1st ` ( ( ( Q PoolAlg %s ) ` Z ) ` %s ) )' % (X5, k)

w = WH('a5ks', 'The scan halts at a shift with a large enough pool (Lean: scan_spec applied in SearchAlg.lean).')
h1 = w.h('( Q e. Word NN0 /\\ Z e. NN0 /\\ H e. NN0 )')
h2 = w.h('( K e. NN /\\ %s e. NN0 )' % X5)
h3 = w.h('K <_ %s' % X5)
h4 = w.h('( 1st ` ( Q CoprimeTo K ) ) = 1o')
h5 = w.h('H <_ ( # ` %s )' % PGA('K'))
h6 = w.h('J = %s' % SCN)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
qcl = st([h1], 'simp1d', 'Q e. Word NN0')
zn0 = st([h1], 'simp2d', 'Z e. NN0')
hn0 = st([h1], 'simp3d', 'H e. NN0')
knn = st([h2], 'simpld', 'K e. NN')
x5n = st([h2], 'simprd', '%s e. NN0' % X5)
spec = st([st([st([qcl, x5n, zn0], '3jca', '( Q e. Word NN0 /\\ %s e. NN0 /\\ Z e. NN0 )' % X5),
              st([hn0, knn, x5n], '3jca', '( H e. NN0 /\\ K e. NN /\\ %s e. NN0 )' % X5),
              st([h3, h4, h5], '3jca', '( K <_ %s /\\ ( 1st ` ( Q CoprimeTo K ) ) = 1o /\\ H <_ ( # ` %s ) )' % (X5, PGA('K')))],
             '3jca',
             '( ( Q e. Word NN0 /\\ %s e. NN0 /\\ Z e. NN0 ) /\\ ( H e. NN0 /\\ K e. NN /\\ %s e. NN0 ) /\\ ( K <_ %s /\\ ( 1st ` ( Q CoprimeTo K ) ) = 1o /\\ H <_ ( # ` %s ) ) )' % (X5, X5, X5, PGA('K'))),
           w.inst('scanspec')], 'syl',
          '( ( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ ( 1 <_ %s /\\ %s <_ K ) ) /\\ ( ( ( 1st ` ( Q CoprimeTo %s ) ) = 1o /\\ H <_ ( # ` %s ) ) /\\ ( %s = %s /\\ ( 2nd ` %s ) <_ ( %s x. %s ) ) ) )'
          % (SCN, KS, KS, KS, PS, PS, PGA(KS), SCN, KS, CB))
a = st([spec], 'simpld', '( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ ( 1 <_ %s /\\ %s <_ K ) )' % (SCN, KS, KS))
b = st([spec], 'simprd', '( ( ( 1st ` ( Q CoprimeTo %s ) ) = 1o /\\ H <_ ( # ` %s ) ) /\\ ( %s = %s /\\ ( 2nd ` %s ) <_ ( %s x. %s ) ) )' % (KS, PS, PS, PGA(KS), SCN, KS, CB))
sne = st([a], 'simpld', '( 1st ` %s ) =/= ( inr ` (/) )' % SCN)
s1le = st([st([a], 'simprd', '( 1 <_ %s /\\ %s <_ K )' % (KS, KS))], 'simpld', '1 <_ %s' % KS)
skle = st([st([a], 'simprd', '( 1 <_ %s /\\ %s <_ K )' % (KS, KS))], 'simprd', '%s <_ K' % KS)
scop = st([st([b], 'simpld', '( ( 1st ` ( Q CoprimeTo %s ) ) = 1o /\\ H <_ ( # ` %s ) )' % (KS, PS))], 'simpld',
          '( 1st ` ( Q CoprimeTo %s ) ) = 1o' % KS)
sh = st([st([b], 'simpld', '( ( 1st ` ( Q CoprimeTo %s ) ) = 1o /\\ H <_ ( # ` %s ) )' % (KS, PS))], 'simprd',
        'H <_ ( # ` %s )' % PS)
spd = st([st([b], 'simprd', '( %s = %s /\\ ( 2nd ` %s ) <_ ( %s x. %s ) )' % (PS, PGA(KS), SCN, KS, CB))], 'simpld',
         '%s = %s' % (PS, PGA(KS)))
scst = st([st([b], 'simprd', '( %s = %s /\\ ( 2nd ` %s ) <_ ( %s x. %s ) )' % (PS, PGA(KS), SCN, KS, CB))], 'simprd',
          '( 2nd ` %s ) <_ ( %s x. %s )' % (SCN, KS, CB))
# transfer along J = SCN
jeq = st([h6], 'eqcomd', '%s = J' % SCN)
f1 = w.s([jeq], 'fveq2d', '( ph -> ( 1st ` %s ) = ( 1st ` J ) )' % SCN)
f2 = w.s([f1], 'fveq2d', '( ph -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % SCN)
kke = w.s([f2], 'fveq2d', '( ph -> %s = %s )' % (KS, KJ))
ppe = w.s([f2], 'fveq2d', '( ph -> %s = %s )' % (PS, PJ))
c2 = w.s([jeq], 'fveq2d', '( ph -> ( 2nd ` %s ) = ( 2nd ` J ) )' % SCN)
jne = st([f1, sne], 'eqnetrrd', '( 1st ` J ) =/= ( inr ` (/) )')
j1le = st([s1le, kke], 'breqtrd', '1 <_ %s' % KJ)
jkle = st([kke, skle], 'eqbrtrrd', '%s <_ K' % KJ)
jcop = st([w.s([w.s([kke], 'oveq2d', '( ph -> ( Q CoprimeTo %s ) = ( Q CoprimeTo %s ) )' % (KS, KJ))], 'fveq2d',
               '( ph -> ( 1st ` ( Q CoprimeTo %s ) ) = ( 1st ` ( Q CoprimeTo %s ) ) )' % (KS, KJ)), scop],
          'eqtr3d', '( 1st ` ( Q CoprimeTo %s ) ) = 1o' % KJ)
jh = st([sh, w.s([ppe], 'fveq2d', '( ph -> ( # ` %s ) = ( # ` %s ) )' % (PS, PJ))], 'breqtrd', 'H <_ ( # ` %s )' % PJ)
pge = w.s([w.s([kke], 'fveq2d', '( ph -> ( ( ( Q PoolAlg %s ) ` Z ) ` %s ) = ( ( ( Q PoolAlg %s ) ` Z ) ` %s ) )' % (X5, KS, X5, KJ))],
          'fveq2d', '( ph -> %s = %s )' % (PGA(KS), PGA(KJ)))
jpd = st([st([st([ppe], 'eqcomd', '%s = %s' % (PJ, PS)), spd], 'eqtrd', '%s = %s' % (PJ, PGA(KS))), pge],
         'eqtrd', '%s = %s' % (PJ, PGA(KJ)))
jcst = st([st([c2, scst], 'eqbrtrrd', '( 2nd ` J ) <_ ( %s x. %s )' % (KS, CB)),
           w.s([kke], 'oveq1d', '( ph -> ( %s x. %s ) = ( %s x. %s ) )' % (KS, CB, KJ, CB))], 'breqtrd',
          '( 2nd ` J ) <_ ( %s x. %s )' % (KJ, CB))
# typing of the payload
scl = st([st([st([st([qcl, x5n], 'jca', '( Q e. Word NN0 /\\ %s e. NN0 )' % X5), zn0], 'jca',
                  '( ( Q e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 )' % X5), hn0], 'jca',
                 '( ( ( Q e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 ) /\\ H e. NN0 )' % X5),
              w.s([num.fact(w, '1', 'NN0')], 'a1i', '( ph -> 1 e. NN0 )')], 'jca',
             '( ( ( ( Q e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 ) /\\ H e. NN0 ) /\\ 1 e. NN0 )' % X5)
scl2 = st([st([scl, x5n], 'jca',
              '( ( ( ( ( Q e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 ) /\\ H e. NN0 ) /\\ 1 e. NN0 ) /\\ %s e. NN0 )' % (X5, X5)),
           w.inst('scancl')], 'syl', '%s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )' % SCN)
jcl = st([h6, scl2], 'eqeltrd', 'J e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )')
pay = w.s([jcl, jne], 'a5pay', '( ph -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (KJ, PJ))
kn0 = st([pay], 'simpld', '%s e. NN0' % KJ)
pw = st([pay], 'simprd', '%s e. Word NN0' % PJ)
knn2 = st([st([kn0, j1le], 'jca', '( %s e. NN0 /\\ 1 <_ %s )' % (KJ, KJ)), w.inst('elnnnn0c')], 'sylibr',
          '%s e. NN' % KJ)
w.qed([st([st([jne, st([knn2, jkle], 'jca', '( %s e. NN /\\ %s <_ K )' % (KJ, KJ))], 'jca',
           '( ( 1st ` J ) =/= ( inr ` (/) ) /\\ ( %s e. NN /\\ %s <_ K ) )' % (KJ, KJ)),
          st([pw, jcop], 'jca', '( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o )' % (PJ, KJ))], 'jca',
          '( ( ( 1st ` J ) =/= ( inr ` (/) ) /\\ ( %s e. NN /\\ %s <_ K ) ) /\\ ( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o ) )' % (KJ, KJ, PJ, KJ)),
       st([st([jh, jpd], 'jca', '( H <_ ( # ` %s ) /\\ %s = %s )' % (PJ, PJ, PGA(KJ))), jcst], 'jca',
          '( ( H <_ ( # ` %s ) /\\ %s = %s ) /\\ ( 2nd ` J ) <_ ( %s x. %s ) )' % (PJ, PJ, PGA(KJ), KJ, CB))],
      'jca',
      '( ph -> ( ( ( ( 1st ` J ) =/= ( inr ` (/) ) /\\ ( %s e. NN /\\ %s <_ K ) ) /\\ ( %s e. Word NN0 /\\ ( 1st ` ( Q CoprimeTo %s ) ) = 1o ) ) /\\ ( ( H <_ ( # ` %s ) /\\ %s = %s ) /\\ ( 2nd ` J ) <_ ( %s x. %s ) ) ) )'
      % (KJ, KJ, PJ, KJ, PJ, PJ, PGA(KJ), KJ, CB))
run(w)
