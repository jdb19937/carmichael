"""Sortie C0b, batch 8: the affine function, its primitive, and the
subtraction lemma (gouraffdv, rectintsub0)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

K1 = '( V - ( C x. Z ) )'
TDEF = 'T = ( z e. CC |-> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) )' % K1
SDEF = 'S = ( z e. CC |-> ( V + ( C x. ( z - Z ) ) ) )'
TOP = '( TopOpen ` CCfld )'

w = W('gouraffdv', 'The affine function is the derivative of an explicit quadratic primitive on the complex plane, and is continuous.')
hyp(w, '1', 'gouraffdv.t', TDEF)
hyp(w, '2', 'gouraffdv.s', SDEF)
A0 = '( V e. CC /\\ C e. CC /\\ Z e. CC )'
vc = w.s([], 'simp1', '( %s -> V e. CC )' % A0)
cc = w.s([], 'simp2', '( %s -> C e. CC )' % A0)
zc = w.s([], 'simp3', '( %s -> Z e. CC )' % A0)
k1 = w.s([vc, w.s([cc, zc], 'mulcld', '( %s -> ( C x. Z ) e. CC )' % A0)], 'subcld', '( %s -> %s e. CC )' % (A0, K1))
t2 = closed(w, A0, '2cn', '2 e. CC')
t2n = closed(w, A0, '2ne0', '2 =/= 0')
ch = w.s([cc, t2, t2n], 'divcld', '( %s -> ( C / 2 ) e. CC )' % A0)
prc = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
AZ = '( %s /\\ z e. CC )' % A0
zz = w.s([], 'simpr', '( %s -> z e. CC )' % AZ)
onec = closed(w, AZ, 'ax-1cn', '1 e. CC')
d1 = w.s([prc], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)
d2 = w.s([prc, zz, onec, d1, k1], 'dvmptcmul', '( %s -> ( CC _D ( z e. CC |-> ( %s x. z ) ) ) = ( z e. CC |-> ( %s x. 1 ) ) )' % (A0, K1, K1))
d2b = w.s([d2, w.s([w.s([k1], 'adantr', '( %s -> %s e. CC )' % (AZ, K1))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AZ, K1, K1))], 'eqtrd' if False else 'eqtrd', 'x')
w.lines.pop()
mp1 = w.s([w.s([w.s([k1], 'adantr', '( %s -> %s e. CC )' % (AZ, K1))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AZ, K1, K1))], 'mpteq2dva', '( %s -> ( z e. CC |-> ( %s x. 1 ) ) = ( z e. CC |-> %s ) )' % (A0, K1, K1))
d2b = w.s([d2, mp1], 'eqtrd', '( %s -> ( CC _D ( z e. CC |-> ( %s x. z ) ) ) = ( z e. CC |-> %s ) )' % (A0, K1, K1))
# the square
t2nn = closed(w, A0, '2nn', '2 e. NN')
de = w.s([t2nn, w.inst('dvexp')], 'syl', '( %s -> ( CC _D ( x e. CC |-> ( x ^ 2 ) ) ) = ( x e. CC |-> ( 2 x. ( x ^ ( 2 - 1 ) ) ) ) )' % A0)
cb1 = w.s([w.s([], 'oveq1', '( x = z -> ( x ^ 2 ) = ( z ^ 2 ) )')], 'cbvmptv', '( x e. CC |-> ( x ^ 2 ) ) = ( z e. CC |-> ( z ^ 2 ) )')
cb2 = w.s([w.s([w.s([], 'oveq1', '( x = z -> ( x ^ ( 2 - 1 ) ) = ( z ^ ( 2 - 1 ) ) )')], 'oveq2d', '( x = z -> ( 2 x. ( x ^ ( 2 - 1 ) ) ) = ( 2 x. ( z ^ ( 2 - 1 ) ) ) )')], 'cbvmptv',
          '( x e. CC |-> ( 2 x. ( x ^ ( 2 - 1 ) ) ) ) = ( z e. CC |-> ( 2 x. ( z ^ ( 2 - 1 ) ) ) )')
de2 = w.s([w.s([w.s([cb1], 'oveq2i', '( CC _D ( x e. CC |-> ( x ^ 2 ) ) ) = ( CC _D ( z e. CC |-> ( z ^ 2 ) ) )')], 'eqcomi', '( CC _D ( z e. CC |-> ( z ^ 2 ) ) ) = ( CC _D ( x e. CC |-> ( x ^ 2 ) ) )')], 'a1i',
           '( %s -> ( CC _D ( z e. CC |-> ( z ^ 2 ) ) ) = ( CC _D ( x e. CC |-> ( x ^ 2 ) ) ) )' % A0)
de3 = w.s([w.s([de2, de], 'eqtrd', '( %s -> ( CC _D ( z e. CC |-> ( z ^ 2 ) ) ) = ( x e. CC |-> ( 2 x. ( x ^ ( 2 - 1 ) ) ) ) )' % A0), w.s([cb2], 'a1i', '( %s -> ( x e. CC |-> ( 2 x. ( x ^ ( 2 - 1 ) ) ) ) = ( z e. CC |-> ( 2 x. ( z ^ ( 2 - 1 ) ) ) ) )' % A0)], 'eqtrd',
           '( %s -> ( CC _D ( z e. CC |-> ( z ^ 2 ) ) ) = ( z e. CC |-> ( 2 x. ( z ^ ( 2 - 1 ) ) ) ) )' % A0)
sm = w.s([w.s([w.s([closed(w, AZ, '2m1e1', '( 2 - 1 ) = 1')], 'oveq2d', '( %s -> ( z ^ ( 2 - 1 ) ) = ( z ^ 1 ) )' % AZ), w.s([zz], 'exp1d', '( %s -> ( z ^ 1 ) = z )' % AZ)], 'eqtrd', '( %s -> ( z ^ ( 2 - 1 ) ) = z )' % AZ)], 'oveq2d',
         '( %s -> ( 2 x. ( z ^ ( 2 - 1 ) ) ) = ( 2 x. z ) )' % AZ)
de4 = w.s([de3, w.s([sm], 'mpteq2dva', '( %s -> ( z e. CC |-> ( 2 x. ( z ^ ( 2 - 1 ) ) ) ) = ( z e. CC |-> ( 2 x. z ) ) )' % A0)], 'eqtrd',
          '( %s -> ( CC _D ( z e. CC |-> ( z ^ 2 ) ) ) = ( z e. CC |-> ( 2 x. z ) ) )' % A0)
sq = w.s([zz, closed(w, AZ, '2nn0', '2 e. NN0')], 'expcld', '( %s -> ( z ^ 2 ) e. CC )' % AZ)
tz = w.s([closed(w, AZ, '2cn', '2 e. CC'), zz], 'mulcld', '( %s -> ( 2 x. z ) e. CC )' % AZ)
d4 = w.s([prc, sq, tz, de4, ch], 'dvmptcmul', '( %s -> ( CC _D ( z e. CC |-> ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) = ( z e. CC |-> ( ( C / 2 ) x. ( 2 x. z ) ) ) )' % A0)
ccz = w.s([cc], 'adantr', '( %s -> C e. CC )' % AZ)
chz = w.s([ch], 'adantr', '( %s -> ( C / 2 ) e. CC )' % AZ)
cn1 = w.s([w.s([chz, closed(w, AZ, '2cn', '2 e. CC'), zz], 'mulassd', '( %s -> ( ( ( C / 2 ) x. 2 ) x. z ) = ( ( C / 2 ) x. ( 2 x. z ) ) )' % AZ)], 'eqcomd',
          '( %s -> ( ( C / 2 ) x. ( 2 x. z ) ) = ( ( ( C / 2 ) x. 2 ) x. z ) )' % AZ)
cn2 = w.s([w.s([ccz, closed(w, AZ, '2cn', '2 e. CC'), closed(w, AZ, '2ne0', '2 =/= 0')], 'divcan2d', '( %s -> ( 2 x. ( C / 2 ) ) = C )' % AZ)], 'eqcomd', '( %s -> C = ( 2 x. ( C / 2 ) ) )' % AZ)
cmm = w.s([chz, closed(w, AZ, '2cn', '2 e. CC')], 'mulcomd', '( %s -> ( ( C / 2 ) x. 2 ) = ( 2 x. ( C / 2 ) ) )' % AZ)
cn3 = w.s([cn1, w.s([w.s([cmm, w.s([cn2], 'eqcomd', '( %s -> ( 2 x. ( C / 2 ) ) = C )' % AZ)], 'eqtrd', '( %s -> ( ( C / 2 ) x. 2 ) = C )' % AZ)], 'oveq1d', '( %s -> ( ( ( C / 2 ) x. 2 ) x. z ) = ( C x. z ) )' % AZ)], 'eqtrd',
          '( %s -> ( ( C / 2 ) x. ( 2 x. z ) ) = ( C x. z ) )' % AZ)
d4b = w.s([d4, w.s([cn3], 'mpteq2dva', '( %s -> ( z e. CC |-> ( ( C / 2 ) x. ( 2 x. z ) ) ) = ( z e. CC |-> ( C x. z ) ) )' % A0)], 'eqtrd',
          '( %s -> ( CC _D ( z e. CC |-> ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) = ( z e. CC |-> ( C x. z ) ) )' % A0)
k1z = w.s([k1], 'adantr', '( %s -> %s e. CC )' % (AZ, K1))
d5 = w.s([prc, w.s([k1z, zz], 'mulcld', '( %s -> ( %s x. z ) e. CC )' % (AZ, K1)), k1z, d2b,
          w.s([chz, sq], 'mulcld', '( %s -> ( ( C / 2 ) x. ( z ^ 2 ) ) e. CC )' % AZ), w.s([ccz, zz], 'mulcld', '( %s -> ( C x. z ) e. CC )' % AZ), d4b], 'dvmptadd',
         '( %s -> ( CC _D ( z e. CC |-> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) ) = ( z e. CC |-> ( %s + ( C x. z ) ) ) )' % (A0, K1, K1))
tdv = w.s([w.s(['1'], 'a1i', '( %s -> %s )' % (A0, TDEF)), d5], 'eqtrdi' if False else 'eqtrd', 'x')
w.lines.pop()
teq = w.s([w.s(['1'], 'a1i', '( %s -> %s )' % (A0, TDEF))], 'oveq2d', '( %s -> ( CC _D T ) = ( CC _D ( z e. CC |-> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) ) )' % (A0, K1))
tdv = w.s([teq, d5], 'eqtrd', '( %s -> ( CC _D T ) = ( z e. CC |-> ( %s + ( C x. z ) ) ) )' % (A0, K1))
# S equals that mapping
vcz = w.s([vc], 'adantr', '( %s -> V e. CC )' % AZ)
zcz = w.s([zc], 'adantr', '( %s -> Z e. CC )' % AZ)
a1 = w.s([ccz, zz, zcz], 'subdid', '( %s -> ( C x. ( z - Z ) ) = ( ( C x. z ) - ( C x. Z ) ) )' % AZ)
a2 = w.s([a1], 'oveq2d', '( %s -> ( V + ( C x. ( z - Z ) ) ) = ( V + ( ( C x. z ) - ( C x. Z ) ) ) )' % AZ)
a3 = w.s([w.s([vcz, w.s([ccz, zz], 'mulcld', '( %s -> ( C x. z ) e. CC )' % AZ), w.s([ccz, zcz], 'mulcld', '( %s -> ( C x. Z ) e. CC )' % AZ)], 'addsubassd',
              '( %s -> ( ( V + ( C x. z ) ) - ( C x. Z ) ) = ( V + ( ( C x. z ) - ( C x. Z ) ) ) )' % AZ)], 'eqcomd',
         '( %s -> ( V + ( ( C x. z ) - ( C x. Z ) ) ) = ( ( V + ( C x. z ) ) - ( C x. Z ) ) )' % AZ)
a4 = w.s([vcz, w.s([ccz, zz], 'mulcld', '( %s -> ( C x. z ) e. CC )' % AZ), w.s([ccz, zcz], 'mulcld', '( %s -> ( C x. Z ) e. CC )' % AZ)], 'addsubd',
         '( %s -> ( ( V + ( C x. z ) ) - ( C x. Z ) ) = ( %s + ( C x. z ) ) )' % (AZ, K1))
seq = w.s([w.s(['2'], 'a1i', '( %s -> %s )' % (A0, SDEF)), w.s([w.s([w.s([a2, a3], 'eqtrd', '( %s -> ( V + ( C x. ( z - Z ) ) ) = ( ( V + ( C x. z ) ) - ( C x. Z ) ) )' % AZ), a4], 'eqtrd', '( %s -> ( V + ( C x. ( z - Z ) ) ) = ( %s + ( C x. z ) ) )' % (AZ, K1))], 'mpteq2dva',
           '( %s -> ( z e. CC |-> ( V + ( C x. ( z - Z ) ) ) ) = ( z e. CC |-> ( %s + ( C x. z ) ) ) )' % (A0, K1))], 'eqtrd', '( %s -> S = ( z e. CC |-> ( %s + ( C x. z ) ) ) )' % (A0, K1))
dvs = w.s([tdv, seq], 'eqtr4d', '( %s -> ( CC _D T ) = S )' % A0)
# T maps CC into CC
tf = w.s([w.s(['1'], 'a1i', '( %s -> %s )' % (A0, TDEF)), w.s([w.s([w.s([k1z, zz], 'mulcld', '( %s -> ( %s x. z ) e. CC )' % (AZ, K1)), w.s([chz, sq], 'mulcld', '( %s -> ( ( C / 2 ) x. ( z ^ 2 ) ) e. CC )' % AZ)], 'addcld',
          '( %s -> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) e. CC )' % (AZ, K1))], 'fmptd', '( %s -> ( z e. CC |-> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) : CC --> CC )' % (A0, K1))], 'feq1d' if False else 'eqeltrrd', 'x')
w.lines.pop()
tfm = w.s([w.s([w.s([k1z, zz], 'mulcld', '( %s -> ( %s x. z ) e. CC )' % (AZ, K1)), w.s([chz, sq], 'mulcld', '( %s -> ( ( C / 2 ) x. ( z ^ 2 ) ) e. CC )' % AZ)], 'addcld',
               '( %s -> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) e. CC )' % (AZ, K1))], 'fmptd', '( %s -> ( z e. CC |-> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) : CC --> CC )' % (A0, K1))
tf = w.s([w.s([w.s(['1'], 'a1i', '( %s -> %s )' % (A0, TDEF))], 'feq1d', '( %s -> ( T : CC --> CC <-> ( z e. CC |-> ( ( %s x. z ) + ( ( C / 2 ) x. ( z ^ 2 ) ) ) ) : CC --> CC ) )' % (A0, K1)), tfm], 'mpbird', '( %s -> T : CC --> CC )' % A0)
# S is continuous on CC
sscc = closed(w, A0, 'ssid', 'CC C_ CC')
je = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
addc = w.s([je], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
subc = w.s([je], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
mulc = w.s([je], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
cv = w.s([vc, sscc, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. CC |-> V ) e. ( CC -cn-> CC ) )' % A0)
cC = w.s([cc, sscc, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. CC |-> C ) e. ( CC -cn-> CC ) )' % A0)
cZ = w.s([zc, sscc, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. CC |-> Z ) e. ( CC -cn-> CC ) )' % A0)
cid = w.s([sscc, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( z e. CC |-> z ) e. ( CC -cn-> CC ) )' % A0)
csub = w.s([je, w.s([subc], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cid, cZ], 'cncfmpt2f', '( %s -> ( z e. CC |-> ( z - Z ) ) e. ( CC -cn-> CC ) )' % A0)
cmul = w.s([je, w.s([mulc], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cC, csub], 'cncfmpt2f', '( %s -> ( z e. CC |-> ( C x. ( z - Z ) ) ) e. ( CC -cn-> CC ) )' % A0)
cadd = w.s([je, w.s([addc], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cv, cmul], 'cncfmpt2f', '( %s -> ( z e. CC |-> ( V + ( C x. ( z - Z ) ) ) ) e. ( CC -cn-> CC ) )' % A0)
scn = w.s([w.s(['2'], 'a1i', '( %s -> %s )' % (A0, SDEF)), cadd], 'eqeltrd', '( %s -> S e. ( CC -cn-> CC ) )' % A0)
w.qed([w.s([tf, dvs], 'jca', '( %s -> ( T : CC --> CC /\\ ( CC _D T ) = S ) )' % A0), scn], 'jca',
      '( %s -> ( ( T : CC --> CC /\\ ( CC _D T ) = S ) /\\ S e. ( CC -cn-> CC ) ) )' % A0)
run(w, True)


# ---- rectintsub0: subtracting a function with a primitive on the plane
w = W('rectintsub0', 'A boundary integral is unchanged by subtracting a function that has a primitive on the whole plane.')
HYP = '( O e. ( D -cn-> CC ) /\\ ( T : CC --> CC /\\ ( CC _D T ) = S ) /\\ S e. ( CC -cn-> CC ) )'
EQR = 'A. w e. ( A crect B ) ( F ` w ) = ( ( O ` w ) + ( S ` w ) )'
A0 = '( %s /\\ %s /\\ %s )' % (PS, HYP, EQR)
d = ctx(w, A0)
hy = w.s([], 'simp2', '( %s -> %s )' % (A0, HYP))
al = w.s([], 'simp3', '( %s -> %s )' % (A0, EQR))
ocn = w.s([hy, w.inst('simp1')], 'syl', '( %s -> O e. ( D -cn-> CC ) )' % A0)
tpr = w.s([hy, w.inst('simp2')], 'syl', '( %s -> ( T : CC --> CC /\\ ( CC _D T ) = S ) )' % A0)
scn = w.s([hy, w.inst('simp3')], 'syl', '( %s -> S e. ( CC -cn-> CC ) )' % A0)
dss = w.s([d['fcn'], w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
rcc = w.s([d['ab'], w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
SR = '( S |` D )'
sri = w.s([dss, w.inst('rescncf')], 'syl', '( %s -> ( S e. ( CC -cn-> CC ) -> %s e. ( D -cn-> CC ) ) )' % (A0, SR))
srcn = w.s([scn, sri], 'mpd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, SR))
AZ = '( %s /\\ z e. ( A crect B ) )' % A0
zr = w.s([], 'simpr', '( %s -> z e. ( A crect B ) )' % AZ)
zd = w.s([w.s([d['rss']], 'adantr', '( %s -> ( A crect B ) C_ D )' % AZ), zr], 'sseldd', '( %s -> z e. D )' % AZ)
frv = w.s([zd, w.inst('fvres')], 'syl', '( %s -> ( %s ` z ) = ( S ` z ) )' % (AZ, SR))
sub = w.s([w.s([], 'fveq2', '( w = z -> ( F ` w ) = ( F ` z ) )'),
           w.s([w.s([], 'fveq2', '( w = z -> ( O ` w ) = ( O ` z ) )'), w.s([], 'fveq2', '( w = z -> ( S ` w ) = ( S ` z ) )')], 'oveq12d', '( w = z -> ( ( O ` w ) + ( S ` w ) ) = ( ( O ` z ) + ( S ` z ) ) )')], 'eqeq12d',
          '( w = z -> ( ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) <-> ( F ` z ) = ( ( O ` z ) + ( S ` z ) ) ) )')
ptw = w.s([sub, w.s([al], 'adantr', '( %s -> %s )' % (AZ, EQR)), zr], 'rspcdva', '( %s -> ( F ` z ) = ( ( O ` z ) + ( S ` z ) ) )' % AZ)
ptw2 = w.s([ptw, w.s([w.s([frv], 'eqcomd', '( %s -> ( S ` z ) = ( %s ` z ) )' % (AZ, SR))], 'oveq2d', '( %s -> ( ( O ` z ) + ( S ` z ) ) = ( ( O ` z ) + ( %s ` z ) ) )' % (AZ, SR))], 'eqtrd',
           '( %s -> ( F ` z ) = ( ( O ` z ) + ( %s ` z ) ) )' % (AZ, SR))
ral2 = w.s([ptw2], 'ralrimiva', '( %s -> A. z e. ( A crect B ) ( F ` z ) = ( ( O ` z ) + ( %s ` z ) ) )' % (A0, SR))
psx = w.s([d['ab'], d['geo'], w.s([d['fcn'], d['rss']], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
add2 = w.s([psx, w.s([ocn, srcn], 'jca', '( %s -> ( O e. ( D -cn-> CC ) /\\ %s e. ( D -cn-> CC ) ) )' % (A0, SR)), ral2, w.inst('rectintadd2')], 'syl3anc',
           '( %s -> ( F rectint <. A , B >. ) = ( ( O rectint <. A , B >. ) + ( %s rectint <. A , B >. ) ) )' % (A0, SR))
srex = w.s([srcn, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, SR))
sex = w.s([scn, w.inst('elex')], 'syl', '( %s -> S e. _V )' % A0)
eqi = w.s([w.s([d['ab'], d['geo'], w.s([srex, sex], 'jca', '( %s -> ( %s e. _V /\\ S e. _V ) )' % (A0, SR))], '3jca',
                '( %s -> ( ( A e. CC /\\ B e. CC ) /\\ %s /\\ ( %s e. _V /\\ S e. _V ) ) )' % (A0, GEO, SR)),
           w.s([frv], 'ralrimiva', '( %s -> A. z e. ( A crect B ) ( %s ` z ) = ( S ` z ) )' % (A0, SR)), w.inst('rectinteq')], 'syl2anc',
          '( %s -> ( %s rectint <. A , B >. ) = ( S rectint <. A , B >. ) )' % (A0, SR))
ftc = w.s([d['ab'], d['geo'], w.s([tpr, w.s([scn, rcc], 'jca', '( %s -> ( S e. ( CC -cn-> CC ) /\\ ( A crect B ) C_ CC ) )' % A0)], 'jca',
                                  '( %s -> ( ( T : CC --> CC /\\ ( CC _D T ) = S ) /\\ ( S e. ( CC -cn-> CC ) /\\ ( A crect B ) C_ CC ) ) )' % A0), w.inst('rectintftc')], 'syl3anc',
          '( %s -> ( S rectint <. A , B >. ) = 0 )' % A0)
zero = w.s([eqi, ftc], 'eqtrd', '( %s -> ( %s rectint <. A , B >. ) = 0 )' % (A0, SR))
psO = w.s([d['ab'], d['geo'], w.s([ocn, d['rss']], 'jca', '( %s -> ( O e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )' % A0)], '3jca', '( %s -> %s )' % (A0, PSOF('A', 'B').replace('F e. (', 'O e. (')))
ocl = w.s([psO, w.inst('rectintcl')], 'syl', '( %s -> ( O rectint <. A , B >. ) e. CC )' % A0)
w.qed([add2, w.s([w.s([zero], 'oveq2d', '( %s -> ( ( O rectint <. A , B >. ) + ( %s rectint <. A , B >. ) ) = ( ( O rectint <. A , B >. ) + 0 ) )' % (A0, SR)),
                  w.s([ocl], 'addridd', '( %s -> ( ( O rectint <. A , B >. ) + 0 ) = ( O rectint <. A , B >. ) )' % A0)], 'eqtrd',
                 '( %s -> ( ( O rectint <. A , B >. ) + ( %s rectint <. A , B >. ) ) = ( O rectint <. A , B >. ) )' % (A0, SR))], 'eqtrd',
      '( %s -> ( F rectint <. A , B >. ) = ( O rectint <. A , B >. ) )' % A0)
run(w)


# ---- gourrem: the remainder function is continuous and splits F
AFF = '( V + ( C x. ( z - Z ) ) )'
ODEF = 'O = ( z e. D |-> ( ( F ` z ) - %s ) )' % AFF
w = W('gourrem', 'The remainder of the linear approximation is continuous and splits the function.')
hyp(w, '1', 'gourrem.o', ODEF)
hyp(w, '2', 'gourrem.s', SDEF)
A0 = '( F e. ( D -cn-> CC ) /\\ ( V e. CC /\\ C e. CC /\\ Z e. CC ) )'
fcn = w.s([], 'simpl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
vc = w.s([], 'simpr1', '( %s -> V e. CC )' % A0)
cc = w.s([], 'simpr2', '( %s -> C e. CC )' % A0)
zc = w.s([], 'simpr3', '( %s -> Z e. CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
sscc = closed(w, A0, 'ssid', 'CC C_ CC')
je = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
subc = w.s([je], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
mulc = w.s([je], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
addc = w.s([je], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
cv = w.s([vc, dss, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. D |-> V ) e. ( D -cn-> CC ) )' % A0)
cC = w.s([cc, dss, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. D |-> C ) e. ( D -cn-> CC ) )' % A0)
cZ = w.s([zc, dss, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. D |-> Z ) e. ( D -cn-> CC ) )' % A0)
cid = w.s([dss, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( z e. D |-> z ) e. ( D -cn-> CC ) )' % A0)
csub = w.s([je, w.s([subc], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cid, cZ], 'cncfmpt2f', '( %s -> ( z e. D |-> ( z - Z ) ) e. ( D -cn-> CC ) )' % A0)
cmul = w.s([je, w.s([mulc], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cC, csub], 'cncfmpt2f', '( %s -> ( z e. D |-> ( C x. ( z - Z ) ) ) e. ( D -cn-> CC ) )' % A0)
caff = w.s([je, w.s([addc], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cv, cmul], 'cncfmpt2f', '( %s -> ( z e. D |-> %s ) e. ( D -cn-> CC ) )' % (A0, AFF))
fmp = w.s([ff], 'feqmptd', '( %s -> F = ( z e. D |-> ( F ` z ) ) )' % A0)
cf = w.s([w.s([fmp], 'eqcomd', '( %s -> ( z e. D |-> ( F ` z ) ) = F )' % A0), fcn], 'eqeltrd', '( %s -> ( z e. D |-> ( F ` z ) ) e. ( D -cn-> CC ) )' % A0)
cO = w.s([je, w.s([subc], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP)), cf, caff], 'cncfmpt2f', '( %s -> ( z e. D |-> ( ( F ` z ) - %s ) ) e. ( D -cn-> CC ) )' % (A0, AFF))
ocn = w.s([w.s(['1'], 'a1i', '( %s -> %s )' % (A0, ODEF)), cO], 'eqeltrd', '( %s -> O e. ( D -cn-> CC ) )' % A0)
# the pointwise splitting
AW = '( %s /\\ w e. D )' % A0
wd = w.s([], 'simpr', '( %s -> w e. D )' % AW)
wcc = w.s([w.s([dss], 'adantr', '( %s -> D C_ CC )' % AW), wd], 'sseldd', '( %s -> w e. CC )' % AW)
AFFW = '( V + ( C x. ( w - Z ) ) )'
s1 = w.s([], 'oveq1', '( z = w -> ( z - Z ) = ( w - Z ) )')
s2 = w.s([s1], 'oveq2d', '( z = w -> ( C x. ( z - Z ) ) = ( C x. ( w - Z ) ) )')
s3 = w.s([s2], 'oveq2d', '( z = w -> %s = %s )' % (AFF, AFFW))
s4 = w.s([w.s([], 'fveq2', '( z = w -> ( F ` z ) = ( F ` w ) )'), s3], 'oveq12d', '( z = w -> ( ( F ` z ) - %s ) = ( ( F ` w ) - %s ) )' % (AFF, AFFW))
affw = w.s([w.s([vc], 'adantr', '( %s -> V e. CC )' % AW), w.s([w.s([cc], 'adantr', '( %s -> C e. CC )' % AW), w.s([wcc, w.s([zc], 'adantr', '( %s -> Z e. CC )' % AW)], 'subcld', '( %s -> ( w - Z ) e. CC )' % AW)], 'mulcld', '( %s -> ( C x. ( w - Z ) ) e. CC )' % AW)], 'addcld', '( %s -> %s e. CC )' % (AW, AFFW))
fwc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % AW), wd], 'ffvelcdmd', '( %s -> ( F ` w ) e. CC )' % AW)
ov1 = closed(w, AW, 'ovex', '( ( F ` w ) - %s ) e. _V' % AFFW)
oval = w.s([wd, ov1, w.s([s4, '1'], 'fvmptg', '( ( w e. D /\\ ( ( F ` w ) - %s ) e. _V ) -> ( O ` w ) = ( ( F ` w ) - %s ) )' % (AFFW, AFFW))], 'syl2anc',
           '( %s -> ( O ` w ) = ( ( F ` w ) - %s ) )' % (AW, AFFW))
ov2 = closed(w, AW, 'ovex', '%s e. _V' % AFFW)
sval = w.s([wcc, ov2, w.s([s3, '2'], 'fvmptg', '( ( w e. CC /\\ %s e. _V ) -> ( S ` w ) = %s )' % (AFFW, AFFW))], 'syl2anc',
           '( %s -> ( S ` w ) = %s )' % (AW, AFFW))
spl = w.s([w.s([oval, sval], 'oveq12d', '( %s -> ( ( O ` w ) + ( S ` w ) ) = ( ( ( F ` w ) - %s ) + %s ) )' % (AW, AFFW, AFFW)),
           w.s([fwc, affw], 'npcand', '( %s -> ( ( ( F ` w ) - %s ) + %s ) = ( F ` w ) )' % (AW, AFFW, AFFW))], 'eqtrd',
          '( %s -> ( ( O ` w ) + ( S ` w ) ) = ( F ` w ) )' % AW)
ral = w.s([w.s([spl], 'eqcomd', '( %s -> ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) )' % AW)], 'ralrimiva', '( %s -> A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) )' % A0)
w.qed([ocn, ral], 'jca', '( %s -> ( O e. ( D -cn-> CC ) /\\ A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) ) )' % A0)
run(w, True)
