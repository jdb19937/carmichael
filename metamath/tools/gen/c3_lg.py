"""Sortie C3 section 5: the logarithmically weighted Dirichlet series (the
derivative series), by shifting the abscissa."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

RZ = '( Re ` Z )'
LTRM = '( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) )'
SHC = '( q e. NN |-> ( ( ( A ` q ) x. ( log ` q ) ) x. ( q ^c -u E ) ) )'
SHCM = '( ( ( A ` m ) x. ( log ` m ) ) x. ( m ^c -u E ) )'

# ---- dshcval ---------------------------------------------------------------
w = W('dshcval', 'The value of the shifted coefficient function of a logarithmically weighted Dirichlet series.')
A0 = 'K e. NN'
sub = w.s([w.s([w.s([], 'fveq2', '( q = K -> ( A ` q ) = ( A ` K ) )'),
                w.s([], 'fveq2', '( q = K -> ( log ` q ) = ( log ` K ) )')], 'oveq12d',
               '( q = K -> ( ( A ` q ) x. ( log ` q ) ) = ( ( A ` K ) x. ( log ` K ) ) )'),
           w.s([], 'oveq1', '( q = K -> ( q ^c -u E ) = ( K ^c -u E ) )')], 'oveq12d',
          '( q = K -> ( ( ( A ` q ) x. ( log ` q ) ) x. ( q ^c -u E ) ) = ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) )')
em = w.s([], 'eqid', '%s = %s' % (SHC, SHC))
fv = w.s([sub, em], 'fvmptg',
         '( ( K e. NN /\\ ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) e. _V ) -> ( %s ` K ) = ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) )' % SHC)
ex = w.s([w.s([], 'ovex', '( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) e. _V')], 'a1i',
         '( %s -> ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) e. _V )' % A0)
w.qed([w.s([], 'id', '( %s -> K e. NN )' % A0), ex, fv], 'syl2anc',
      '( %s -> ( %s ` K ) = ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) )' % (A0, SHC)); run3(w)

# ---- dshcbnd ---------------------------------------------------------------
w = W('dshcbnd', 'The shifted coefficients of a logarithmically weighted Dirichlet series are bounded.')
A0 = '( ( ( ( A ` K ) e. CC /\\ ( abs ` ( A ` K ) ) <_ C /\\ C e. RR ) /\\ K e. NN ) /\\ E e. RR+ )'
lll = w.s([], 'simpll', '( %s -> ( ( A ` K ) e. CC /\\ ( abs ` ( A ` K ) ) <_ C /\\ C e. RR ) )' % A0)
ak = w.s([lll, w.inst('simp1')], 'syl', '( %s -> ( A ` K ) e. CC )' % A0)
abk = w.s([lll, w.inst('simp2')], 'syl', '( %s -> ( abs ` ( A ` K ) ) <_ C )' % A0)
cr = w.s([lll, w.inst('simp3')], 'syl', '( %s -> C e. RR )' % A0)
kn = w.s([], 'simplr', '( %s -> K e. NN )' % A0)
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
nter = w.s([er], 'renegcld', '( %s -> -u E e. RR )' % A0)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0)
k1 = w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)
kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0)
kne = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)
lkr = w.s([krp, w.inst('relogcl')], 'syl', '( %s -> ( log ` K ) e. RR )' % A0)
lk0 = w.s([kr, k1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` K ) )' % A0)
abkr = w.s([ak], 'abscld', '( %s -> ( abs ` ( A ` K ) ) e. RR )' % A0)
abk0 = w.s([ak], 'absge0d', '( %s -> 0 <_ ( abs ` ( A ` K ) ) )' % A0)
pE = w.s([krp, er], 'rpcxpcld', '( %s -> ( K ^c E ) e. RR+ )' % A0)
pnE = w.s([krp, nter], 'rpcxpcld', '( %s -> ( K ^c -u E ) e. RR+ )' % A0)
pErE = w.s([pE, erp], 'rpdivcld', '( %s -> ( ( K ^c E ) / E ) e. RR+ )' % A0)
lkb = w.s([kn, erp, w.inst('logcxpbnd')], 'syl2anc', '( %s -> ( log ` K ) <_ ( ( K ^c E ) / E ) )' % A0)
# step 1: the modulus of the product of the first two factors
ab1 = w.s([ak, w.s([lkr], 'recnd', '( %s -> ( log ` K ) e. CC )' % A0)], 'absmuld',
          '( %s -> ( abs ` ( ( A ` K ) x. ( log ` K ) ) ) = ( ( abs ` ( A ` K ) ) x. ( abs ` ( log ` K ) ) ) )' % A0)
abl = w.s([lkr, lk0], 'absidd', '( %s -> ( abs ` ( log ` K ) ) = ( log ` K ) )' % A0)
ab1b = w.s([ab1, w.s([abl], 'oveq2d',
                     '( %s -> ( ( abs ` ( A ` K ) ) x. ( abs ` ( log ` K ) ) ) = ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) )' % A0)],
           'eqtrd', '( %s -> ( abs ` ( ( A ` K ) x. ( log ` K ) ) ) = ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) )' % A0)
# step 2
le2 = w.s([abkr, cr, lkr, w.s([pErE], 'rpred', '( %s -> ( ( K ^c E ) / E ) e. RR )' % A0), abk0, lk0, abk, lkb],
          'lemul12ad', '( %s -> ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) <_ ( C x. ( ( K ^c E ) / E ) ) )' % A0)
# step 3
ab2 = w.s([w.s([ak, w.s([lkr], 'recnd', '( %s -> ( log ` K ) e. CC )' % A0)], 'mulcld',
               '( %s -> ( ( A ` K ) x. ( log ` K ) ) e. CC )' % A0),
           w.s([pnE], 'rpcnd', '( %s -> ( K ^c -u E ) e. CC )' % A0)], 'absmuld',
          '( %s -> ( abs ` ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) ) = ( ( abs ` ( ( A ` K ) x. ( log ` K ) ) ) x. ( abs ` ( K ^c -u E ) ) ) )' % A0)
abp = w.s([w.s([pnE], 'rpred', '( %s -> ( K ^c -u E ) e. RR )' % A0),
           w.s([pnE], 'rpge0d', '( %s -> 0 <_ ( K ^c -u E ) )' % A0)], 'absidd',
          '( %s -> ( abs ` ( K ^c -u E ) ) = ( K ^c -u E ) )' % A0)
ab3 = w.s([ab2, w.s([ab1b, abp], 'oveq12d',
                    '( %s -> ( ( abs ` ( ( A ` K ) x. ( log ` K ) ) ) x. ( abs ` ( K ^c -u E ) ) ) = ( ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) x. ( K ^c -u E ) ) )' % A0)],
          'eqtrd',
          '( %s -> ( abs ` ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) ) = ( ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) x. ( K ^c -u E ) ) )' % A0)
# step 4
le4 = w.s([w.s([abkr, lkr], 'remulcld', '( %s -> ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) e. RR )' % A0),
           w.s([cr, w.s([pErE], 'rpred', '( %s -> ( ( K ^c E ) / E ) e. RR )' % A0)], 'remulcld',
               '( %s -> ( C x. ( ( K ^c E ) / E ) ) e. RR )' % A0),
           w.s([pnE], 'rpred', '( %s -> ( K ^c -u E ) e. RR )' % A0),
           w.s([pnE], 'rpge0d', '( %s -> 0 <_ ( K ^c -u E ) )' % A0), le2], 'lemul1ad',
          '( %s -> ( ( ( abs ` ( A ` K ) ) x. ( log ` K ) ) x. ( K ^c -u E ) ) <_ ( ( C x. ( ( K ^c E ) / E ) ) x. ( K ^c -u E ) ) )' % A0)
# step 5: the algebra
ec = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
sum0 = w.s([ec], 'negidd', '( %s -> ( E + -u E ) = 0 )' % A0)
padd = w.s([w.s([kc, kne], 'jca', '( %s -> ( K e. CC /\\ K =/= 0 ) )' % A0), ec,
            w.s([ec], 'negcld', '( %s -> -u E e. CC )' % A0), w.inst('cxpadd')], 'syl3anc',
           '( %s -> ( K ^c ( E + -u E ) ) = ( ( K ^c E ) x. ( K ^c -u E ) ) )' % A0)
p1 = w.s([w.s([w.s([sum0], 'oveq2d', '( %s -> ( K ^c ( E + -u E ) ) = ( K ^c 0 ) )' % A0),
               w.s([kc, w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A0)], 'eqtrd',
              '( %s -> ( K ^c ( E + -u E ) ) = 1 )' % A0), padd], 'eqtr3d',
         '( %s -> ( ( K ^c E ) x. ( K ^c -u E ) ) = 1 )' % A0)
cc = w.s([cr], 'recnd', '( %s -> C e. CC )' % A0)
pEc = w.s([pE], 'rpcnd', '( %s -> ( K ^c E ) e. CC )' % A0)
pnEc = w.s([pnE], 'rpcnd', '( %s -> ( K ^c -u E ) e. CC )' % A0)
ene = w.s([erp], 'rpne0d', '( %s -> E =/= 0 )' % A0)
# ( C x. ( ( K ^c E ) / E ) ) x. ( K ^c -u E ) = ( C / E ) x. ( ( K ^c E ) x. ( K ^c -u E ) ) = C / E
e1 = w.s([cc, pEc, ec, ene], 'divassd', '( %s -> ( ( C x. ( K ^c E ) ) / E ) = ( C x. ( ( K ^c E ) / E ) ) )' % A0)
e2 = w.s([cc, pEc, ec, ene], 'div23d', '( %s -> ( ( C x. ( K ^c E ) ) / E ) = ( ( C / E ) x. ( K ^c E ) ) )' % A0)
e3 = w.s([w.s([e1], 'eqcomd', '( %s -> ( C x. ( ( K ^c E ) / E ) ) = ( ( C x. ( K ^c E ) ) / E ) )' % A0), e2],
         'eqtrd', '( %s -> ( C x. ( ( K ^c E ) / E ) ) = ( ( C / E ) x. ( K ^c E ) ) )' % A0)
cde = w.s([cc, ec, ene], 'divcld', '( %s -> ( C / E ) e. CC )' % A0)
e4 = w.s([w.s([e3], 'oveq1d',
               '( %s -> ( ( C x. ( ( K ^c E ) / E ) ) x. ( K ^c -u E ) ) = ( ( ( C / E ) x. ( K ^c E ) ) x. ( K ^c -u E ) ) )' % A0),
          w.s([cde, pEc, pnEc], 'mulassd',
              '( %s -> ( ( ( C / E ) x. ( K ^c E ) ) x. ( K ^c -u E ) ) = ( ( C / E ) x. ( ( K ^c E ) x. ( K ^c -u E ) ) ) )' % A0)],
         'eqtrd', '( %s -> ( ( C x. ( ( K ^c E ) / E ) ) x. ( K ^c -u E ) ) = ( ( C / E ) x. ( ( K ^c E ) x. ( K ^c -u E ) ) ) )' % A0)
e5 = w.s([e4, w.s([w.s([p1], 'oveq2d', '( %s -> ( ( C / E ) x. ( ( K ^c E ) x. ( K ^c -u E ) ) ) = ( ( C / E ) x. 1 ) )' % A0),
                   w.s([cde], 'mulridd', '( %s -> ( ( C / E ) x. 1 ) = ( C / E ) )' % A0)], 'eqtrd',
                  '( %s -> ( ( C / E ) x. ( ( K ^c E ) x. ( K ^c -u E ) ) ) = ( C / E ) )' % A0)],
         'eqtrd', '( %s -> ( ( C x. ( ( K ^c E ) / E ) ) x. ( K ^c -u E ) ) = ( C / E ) )' % A0)
fin = w.s([ab3, le4], 'eqbrtrd',
          '( %s -> ( abs ` ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) ) <_ ( ( C x. ( ( K ^c E ) / E ) ) x. ( K ^c -u E ) ) )' % A0)
w.qed([fin, e5], 'breqtrd',
      '( %s -> ( abs ` ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u E ) ) ) <_ ( C / E ) )' % A0); run3(w)

# ---- dlogcfb ---------------------------------------------------------------
w = W('dlogcfb', 'The shifted coefficient function of a logarithmically weighted Dirichlet series is bounded.')
A0 = '( %s /\\ E e. RR+ )' % CFB
Am = '( %s /\\ m e. NN )' % A0
Aq = '( %s /\\ q e. NN )' % A0
cfb = w.s([], 'simpl', '( %s -> %s )' % (A0, CFB))
af = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
cr = w.s([cfb, w.inst('simp2')], 'syl', '( %s -> C e. RR )' % A0)
ral = w.s([cfb, w.inst('simp3')], 'syl', '( %s -> A. m e. NN ( abs ` ( A ` m ) ) <_ C )' % A0)
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
cder = w.s([cr, er, w.s([erp], 'rpne0d', '( %s -> E =/= 0 )' % A0)], 'redivcld', '( %s -> ( C / E ) e. RR )' % A0)
# closure of the body
qn = w.s([], 'simpr', '( %s -> q e. NN )' % Aq)
aq = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Aq), qn], 'ffvelcdmd', '( %s -> ( A ` q ) e. CC )' % Aq)
qrp = w.s([qn], 'nnrpd', '( %s -> q e. RR+ )' % Aq)
lq = w.s([w.s([qrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` q ) e. RR )' % Aq)], 'recnd',
         '( %s -> ( log ` q ) e. CC )' % Aq)
pq = w.s([qrp, w.s([w.s([er], 'renegcld', '( %s -> -u E e. RR )' % A0)], 'adantr', '( %s -> -u E e. RR )' % Aq)],
         'rpcxpcld', '( %s -> ( q ^c -u E ) e. RR+ )' % Aq)
bodyc = w.s([w.s([aq, lq], 'mulcld', '( %s -> ( ( A ` q ) x. ( log ` q ) ) e. CC )' % Aq),
             w.s([pq], 'rpcnd', '( %s -> ( q ^c -u E ) e. CC )' % Aq)], 'mulcld',
            '( %s -> ( ( ( A ` q ) x. ( log ` q ) ) x. ( q ^c -u E ) ) e. CC )' % Aq)
ff = w.s([bodyc, w.s([], 'eqid', '%s = %s' % (SHC, SHC))], 'fmptd', '( %s -> %s : NN --> CC )' % (A0, SHC))
# the bound, derived at a working variable distinct from the one the antecedent binds
Ad = '( %s /\\ d e. NN )' % A0
SHCD = '( ( ( A ` d ) x. ( log ` d ) ) x. ( d ^c -u E ) )'
dn = w.s([], 'simpr', '( %s -> d e. NN )' % Ad)
vd = w.s([dn, w.inst('dshcval')], 'syl', '( %s -> ( %s ` d ) = %s )' % (Ad, SHC, SHCD))
ad = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ad), dn], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % Ad)
e1 = w.s([], 'fveq2', '( m = d -> ( A ` m ) = ( A ` d ) )')
e2 = w.s([e1], 'fveq2d', '( m = d -> ( abs ` ( A ` m ) ) = ( abs ` ( A ` d ) ) )')
e3 = w.s([e2], 'breq1d', '( m = d -> ( ( abs ` ( A ` m ) ) <_ C <-> ( abs ` ( A ` d ) ) <_ C ) )')
abd = w.s([e3, w.s([ral], 'adantr', '( %s -> A. m e. NN ( abs ` ( A ` m ) ) <_ C )' % Ad), dn], 'rspcdva',
          '( %s -> ( abs ` ( A ` d ) ) <_ C )' % Ad)
trip = w.s([ad, abd, w.s([cr], 'adantr', '( %s -> C e. RR )' % Ad)], '3jca',
           '( %s -> ( ( A ` d ) e. CC /\\ ( abs ` ( A ` d ) ) <_ C /\\ C e. RR ) )' % Ad)
pair = w.s([trip, dn], 'jca',
           '( %s -> ( ( ( A ` d ) e. CC /\\ ( abs ` ( A ` d ) ) <_ C /\\ C e. RR ) /\\ d e. NN ) )' % Ad)
bn = w.s([pair, w.s([erp], 'adantr', '( %s -> E e. RR+ )' % Ad)], 'jca',
         '( %s -> ( ( ( ( A ` d ) e. CC /\\ ( abs ` ( A ` d ) ) <_ C /\\ C e. RR ) /\\ d e. NN ) /\\ E e. RR+ ) )' % Ad)
bnd = w.s([bn, w.inst('dshcbnd')], 'syl', '( %s -> ( abs ` %s ) <_ ( C / E ) )' % (Ad, SHCD))
bnd2 = w.s([w.s([vd], 'fveq2d', '( %s -> ( abs ` ( %s ` d ) ) = ( abs ` %s ) )' % (Ad, SHC, SHCD)), bnd], 'eqbrtrd',
           '( %s -> ( abs ` ( %s ` d ) ) <_ ( C / E ) )' % (Ad, SHC))
rald = w.s([bnd2], 'ralrimiva', '( %s -> A. d e. NN ( abs ` ( %s ` d ) ) <_ ( C / E ) )' % (A0, SHC))
cb = w.s([w.s([w.s([], 'fveq2', '( d = m -> ( %s ` d ) = ( %s ` m ) )' % (SHC, SHC))], 'fveq2d',
               '( d = m -> ( abs ` ( %s ` d ) ) = ( abs ` ( %s ` m ) ) )' % (SHC, SHC))], 'breq1d',
         '( d = m -> ( ( abs ` ( %s ` d ) ) <_ ( C / E ) <-> ( abs ` ( %s ` m ) ) <_ ( C / E ) ) )' % (SHC, SHC))
cbv = w.s([cb], 'cbvralvw', '( A. d e. NN ( abs ` ( %s ` d ) ) <_ ( C / E ) <-> A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) )' % (SHC, SHC))
ralm = w.s([rald, w.s([cbv], 'a1i', '( %s -> ( A. d e. NN ( abs ` ( %s ` d ) ) <_ ( C / E ) <-> A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) ) )' % (A0, SHC, SHC))],
           'mpbid', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) )' % (A0, SHC))
w.qed([ff, cder, ralm], '3jca',
      '( %s -> ( %s : NN --> CC /\\ ( C / E ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) ) )' % (A0, SHC, SHC)); run3(w)

# ---- dlogtrm ---------------------------------------------------------------
w = W('dlogtrm', 'The term of a logarithmically weighted Dirichlet series as a term of the shifted series.')
A0 = '( ( K e. NN /\\ E e. CC /\\ Z e. CC ) /\\ B e. CC )'
kn = w.s([], 'simpl1', '( %s -> K e. NN )' % A0)
ec = w.s([], 'simpl2', '( %s -> E e. CC )' % A0)
zc = w.s([], 'simpl3', '( %s -> Z e. CC )' % A0)
bc = w.s([], 'simpr', '( %s -> B e. CC )' % A0)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0)
kne = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)
nE = w.s([ec], 'negcld', '( %s -> -u E e. CC )' % A0)
nZE = w.s([w.s([zc, ec], 'subcld', '( %s -> ( Z - E ) e. CC )' % A0)], 'negcld', '( %s -> -u ( Z - E ) e. CC )' % A0)
add = w.s([w.s([kc, kne], 'jca', '( %s -> ( K e. CC /\\ K =/= 0 ) )' % A0), nE, nZE, w.inst('cxpadd')], 'syl3anc',
          '( %s -> ( K ^c ( -u E + -u ( Z - E ) ) ) = ( ( K ^c -u E ) x. ( K ^c -u ( Z - E ) ) ) )' % A0)
# -u E + -u ( Z - E ) = -u Z
ar = w.s([ec, w.s([zc, ec], 'subcld', '( %s -> ( Z - E ) e. CC )' % A0)], 'negdid',
         '( %s -> -u ( E + ( Z - E ) ) = ( -u E + -u ( Z - E ) ) )' % A0)
pn = w.s([ec, zc], 'pncan3d', '( %s -> ( E + ( Z - E ) ) = Z )' % A0)
ee = w.s([w.s([ar], 'eqcomd', '( %s -> ( -u E + -u ( Z - E ) ) = -u ( E + ( Z - E ) ) )' % A0),
          w.s([pn], 'negeqd', '( %s -> -u ( E + ( Z - E ) ) = -u Z )' % A0)], 'eqtrd',
         '( %s -> ( -u E + -u ( Z - E ) ) = -u Z )' % A0)
pe = w.s([w.s([w.s([ee], 'oveq2d', '( %s -> ( K ^c ( -u E + -u ( Z - E ) ) ) = ( K ^c -u Z ) )' % A0)], 'eqcomd',
               '( %s -> ( K ^c -u Z ) = ( K ^c ( -u E + -u ( Z - E ) ) ) )' % A0), add], 'eqtrd',
         '( %s -> ( K ^c -u Z ) = ( ( K ^c -u E ) x. ( K ^c -u ( Z - E ) ) ) )' % A0)
pEc = w.s([kc, nE, w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u E ) e. CC )' % A0)
pZEc = w.s([kc, nZE, w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u ( Z - E ) ) e. CC )' % A0)
ass = w.s([bc, pEc, pZEc], 'mulassd',
          '( %s -> ( ( B x. ( K ^c -u E ) ) x. ( K ^c -u ( Z - E ) ) ) = ( B x. ( ( K ^c -u E ) x. ( K ^c -u ( Z - E ) ) ) ) )' % A0)
w.qed([ass, w.s([w.s([pe], 'oveq2d',
                      '( %s -> ( B x. ( K ^c -u Z ) ) = ( B x. ( ( K ^c -u E ) x. ( K ^c -u ( Z - E ) ) ) ) )' % A0)],
                'eqcomd', '( %s -> ( B x. ( ( K ^c -u E ) x. ( K ^c -u ( Z - E ) ) ) ) = ( B x. ( K ^c -u Z ) ) )' % A0)],
      'eqtrd', '( %s -> ( ( B x. ( K ^c -u E ) ) x. ( K ^c -u ( Z - E ) ) ) = ( B x. ( K ^c -u Z ) ) )' % A0); run3(w)

# ---- dlogser ---------------------------------------------------------------
w = W('dlogser', 'A logarithmically weighted Dirichlet series is the shifted series of the shifted coefficients.')
A0 = '( A : NN --> CC /\\ E e. CC /\\ Z e. CC )'
Ak = '( %s /\\ k e. NN )' % A0
af = w.s([], 'simp1', '( %s -> A : NN --> CC )' % A0)
ec = w.s([], 'simp2', '( %s -> E e. CC )' % A0)
zc = w.s([], 'simp3', '( %s -> Z e. CC )' % A0)
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
SHCK = '( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u E ) )'
LTRMK = '( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) )'
vk = w.s([kn, w.inst('dshcval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, SHC, SHCK))
ak = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ak), kn], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % Ak)
lk = w.s([w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak), w.inst('relogcl')], 'syl',
               '( %s -> ( log ` k ) e. RR )' % Ak)], 'recnd', '( %s -> ( log ` k ) e. CC )' % Ak)
bc = w.s([ak, lk], 'mulcld', '( %s -> ( ( A ` k ) x. ( log ` k ) ) e. CC )' % Ak)
trm = w.s([w.s([w.s([kn, w.s([ec], 'adantr', '( %s -> E e. CC )' % Ak), w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)],
                    '3jca', '( %s -> ( k e. NN /\\ E e. CC /\\ Z e. CC ) )' % Ak), bc], 'jca',
               '( %s -> ( ( k e. NN /\\ E e. CC /\\ Z e. CC ) /\\ ( ( A ` k ) x. ( log ` k ) ) e. CC ) )' % Ak),
           w.inst('dlogtrm')], 'syl',
          '( %s -> ( %s x. ( k ^c -u ( Z - E ) ) ) = %s )' % (Ak, SHCK, LTRMK))
body = w.s([w.s([vk], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) = ( %s x. ( k ^c -u ( Z - E ) ) ) )' % (Ak, SHC, SHCK)),
            trm], 'eqtrd', '( %s -> ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) = %s )' % (Ak, SHC, LTRMK))
w.qed([body], 'sumeq2dv',
      '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) = sum_ k e. NN %s )' % (A0, SHC, LTRMK)); run3(w)

# ---- dlogbnd ---------------------------------------------------------------
w = W('dlogbnd', 'The bound on a logarithmically weighted Dirichlet series to the right of the line one plus the shift.')
A0 = '( ( %s /\\ E e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + E ) < %s ) )' % (CFB, RZ)
LTRMK = '( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) )'
cfbe = w.s([], 'simpl', '( %s -> ( %s /\\ E e. RR+ ) )' % (A0, CFB))
cfb = w.s([cfbe, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
erp = w.s([cfbe, w.inst('simpr')], 'syl', '( %s -> E e. RR+ )' % A0)
af = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
lt = w.s([], 'simprr', '( %s -> ( 1 + E ) < %s )' % (A0, RZ))
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
ec = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
# the shifted abscissa
ree = w.s([er, w.inst('rere')], 'syl', '( %s -> ( Re ` E ) = E )' % A0)
rsub = w.s([w.s([zc, ec, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( Z - E ) ) = ( %s - ( Re ` E ) ) )' % (A0, RZ)),
            w.s([ree], 'oveq2d', '( %s -> ( %s - ( Re ` E ) ) = ( %s - E ) )' % (A0, RZ, RZ))], 'eqtrd',
           '( %s -> ( Re ` ( Z - E ) ) = ( %s - E ) )' % (A0, RZ))
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
gt = w.s([lt, w.s([r1, er, rz], 'ltaddsubd', '( %s -> ( ( 1 + E ) < %s <-> 1 < ( %s - E ) ) )' % (A0, RZ, RZ))],
         'mpbid', '( %s -> 1 < ( %s - E ) )' % (A0, RZ))
gt2 = w.s([gt, w.s([rsub], 'eqcomd', '( %s -> ( %s - E ) = ( Re ` ( Z - E ) ) )' % (A0, RZ))], 'breqtrd',
          '( %s -> 1 < ( Re ` ( Z - E ) ) )' % A0)
cfbs = w.s([cfbe, w.inst('dlogcfb')], 'syl',
           '( %s -> ( %s : NN --> CC /\\ ( C / E ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) ) )' % (A0, SHC, SHC))
pack = w.s([cfbs, w.s([w.s([zc, ec], 'subcld', '( %s -> ( Z - E ) e. CC )' % A0), gt2], 'jca',
                      '( %s -> ( ( Z - E ) e. CC /\\ 1 < ( Re ` ( Z - E ) ) ) )' % A0)], 'jca',
           '( %s -> ( ( %s : NN --> CC /\\ ( C / E ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) ) /\\ ( ( Z - E ) e. CC /\\ 1 < ( Re ` ( Z - E ) ) ) ) )' % (A0, SHC, SHC))
bnd = w.s([pack, w.inst('dserbnd')], 'syl',
          '( %s -> ( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) ) <_ ( ( C / E ) x. ( 1 + ( 1 / ( ( Re ` ( Z - E ) ) - 1 ) ) ) ) )' % (A0, SHC))
ser = w.s([w.s([af, ec, zc], '3jca', '( %s -> ( A : NN --> CC /\\ E e. CC /\\ Z e. CC ) )' % A0), w.inst('dlogser')], 'syl',
          '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) = sum_ k e. NN %s )' % (A0, SHC, LTRMK))
b2 = w.s([w.s([ser], 'fveq2d',
               '( %s -> ( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) ) = ( abs ` sum_ k e. NN %s ) )' % (A0, SHC, LTRMK)),
          bnd], 'eqbrtrrd',
         '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( ( C / E ) x. ( 1 + ( 1 / ( ( Re ` ( Z - E ) ) - 1 ) ) ) ) )' % (A0, LTRMK))
e1 = w.s([rsub], 'oveq1d', '( %s -> ( ( Re ` ( Z - E ) ) - 1 ) = ( ( %s - E ) - 1 ) )' % (A0, RZ))
e2 = w.s([e1], 'oveq2d', '( %s -> ( 1 / ( ( Re ` ( Z - E ) ) - 1 ) ) = ( 1 / ( ( %s - E ) - 1 ) ) )' % (A0, RZ))
e3 = w.s([e2], 'oveq2d', '( %s -> ( 1 + ( 1 / ( ( Re ` ( Z - E ) ) - 1 ) ) ) = ( 1 + ( 1 / ( ( %s - E ) - 1 ) ) ) )' % (A0, RZ))
e4 = w.s([e3], 'oveq2d', '( %s -> ( ( C / E ) x. ( 1 + ( 1 / ( ( Re ` ( Z - E ) ) - 1 ) ) ) ) = ( ( C / E ) x. ( 1 + ( 1 / ( ( %s - E ) - 1 ) ) ) ) )' % (A0, RZ))
w.qed([b2, e4], 'breqtrd',
      '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( ( C / E ) x. ( 1 + ( 1 / ( ( %s - E ) - 1 ) ) ) ) )' % (A0, LTRMK, RZ)); run3(w)

# ---- dlogcl ----------------------------------------------------------------
w = W('dlogcl', 'A logarithmically weighted Dirichlet series is a complex number to the right of the line one plus the shift.')
A0 = '( ( %s /\\ E e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + E ) < %s ) )' % (CFB, RZ)
LTRMK = '( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) )'
cfbe = w.s([], 'simpl', '( %s -> ( %s /\\ E e. RR+ ) )' % (A0, CFB))
cfb = w.s([cfbe, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
erp = w.s([cfbe, w.inst('simpr')], 'syl', '( %s -> E e. RR+ )' % A0)
af = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
lt = w.s([], 'simprr', '( %s -> ( 1 + E ) < %s )' % (A0, RZ))
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
ec = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
ree = w.s([er, w.inst('rere')], 'syl', '( %s -> ( Re ` E ) = E )' % A0)
rsub = w.s([w.s([zc, ec, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( Z - E ) ) = ( %s - ( Re ` E ) ) )' % (A0, RZ)),
            w.s([ree], 'oveq2d', '( %s -> ( %s - ( Re ` E ) ) = ( %s - E ) )' % (A0, RZ, RZ))], 'eqtrd',
           '( %s -> ( Re ` ( Z - E ) ) = ( %s - E ) )' % (A0, RZ))
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
gt = w.s([lt, w.s([r1, er, rz], 'ltaddsubd', '( %s -> ( ( 1 + E ) < %s <-> 1 < ( %s - E ) ) )' % (A0, RZ, RZ))],
         'mpbid', '( %s -> 1 < ( %s - E ) )' % (A0, RZ))
gt2 = w.s([gt, w.s([rsub], 'eqcomd', '( %s -> ( %s - E ) = ( Re ` ( Z - E ) ) )' % (A0, RZ))], 'breqtrd',
          '( %s -> 1 < ( Re ` ( Z - E ) ) )' % A0)
cfbs = w.s([cfbe, w.inst('dlogcfb')], 'syl',
           '( %s -> ( %s : NN --> CC /\\ ( C / E ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) ) )' % (A0, SHC, SHC))
pack = w.s([cfbs, w.s([w.s([zc, ec], 'subcld', '( %s -> ( Z - E ) e. CC )' % A0), gt2], 'jca',
                      '( %s -> ( ( Z - E ) e. CC /\\ 1 < ( Re ` ( Z - E ) ) ) )' % A0)], 'jca',
           '( %s -> ( ( %s : NN --> CC /\\ ( C / E ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) ) /\\ ( ( Z - E ) e. CC /\\ 1 < ( Re ` ( Z - E ) ) ) ) )' % (A0, SHC, SHC))
cl = w.s([pack, w.inst('dsercl')], 'syl',
         '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) e. CC )' % (A0, SHC))
ser = w.s([w.s([af, ec, zc], '3jca', '( %s -> ( A : NN --> CC /\\ E e. CC /\\ Z e. CC ) )' % A0), w.inst('dlogser')], 'syl',
          '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) = sum_ k e. NN %s )' % (A0, SHC, LTRMK))
w.qed([w.s([ser], 'eqcomd', '( %s -> sum_ k e. NN %s = sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( Z - E ) ) ) )' % (A0, LTRMK, SHC)), cl],
      'eqeltrd', '( %s -> sum_ k e. NN %s e. CC )' % (A0, LTRMK)); run3(w)
