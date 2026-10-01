"""C5, Dirichlet instance 2: the derivative-term bound by the shifted abscissa,
the uniform-limit package UH for the Dirichlet term functions, and HOL plus the
derivative of the Dirichlet series on the half-plane."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

D = HP()
SQ = SQF()
E = EH
RZ = '( Re ` Z )'
SHC = '( q e. NN |-> ( ( ( A ` q ) x. ( log ` q ) ) x. ( q ^c -u %s ) ) )' % E
CFBS = '( %s : NN --> CC /\\ ( C / %s ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / %s ) )' % (SHC, E, SHC, E)


def TRMZ(K, z='z'):
    return TRM('A', K, z)


def hypctx(w, A1, hyp=None):
    d = {}
    if hyp is None:
        hyp = w.s([], 'id', '( %s -> %s )' % (A1, HYP))
    d['hyp'] = hyp
    d['cfb'] = cfb = w.s([hyp, w.inst('simpl')], 'syl', '( %s -> %s )' % (A1, CFB))
    tt = w.s([hyp, w.inst('simpr')], 'syl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A1)
    d['tt'] = tt
    d['af'] = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A1)
    d['cr'] = w.s([cfb, w.inst('simp2')], 'syl', '( %s -> C e. RR )' % A1)
    d['tr'] = tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A1)
    d['t1'] = t1 = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 1 < T )' % A1)
    r1 = a1(w, A1, '1re', '1 e. RR')
    d['r1'] = r1
    tm1 = w.s([tr, r1], 'resubcld', '( %s -> ( T - 1 ) e. RR )' % A1)
    pos = w.s([t1, w.s([r1, tr], 'posdifd', '( %s -> ( 1 < T <-> 0 < ( T - 1 ) ) )' % A1)], 'mpbid', '( %s -> 0 < ( T - 1 ) )' % A1)
    d['tm1rp'] = tm1rp = w.s([tm1, pos], 'elrpd', '( %s -> ( T - 1 ) e. RR+ )' % A1)
    d['erp'] = erp = w.s([tm1rp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A1, E))
    d['er'] = er = w.s([erp], 'rpred', '( %s -> %s e. RR )' % (A1, E))
    d['ec'] = w.s([er], 'recnd', '( %s -> %s e. CC )' % (A1, E))
    d['tme'] = w.s([tr, er], 'resubcld', '( %s -> ( T - %s ) e. RR )' % (A1, E))
    # 1 < ( T - E )
    lt = w.s([tm1rp, w.inst('rphalflt')], 'syl', '( %s -> %s < ( T - 1 ) )' % (A1, E))
    bi = w.s([er, tm1, tr], 'ltsub2d', '( %s -> ( %s < ( T - 1 ) <-> ( T - ( T - 1 ) ) < ( T - %s ) ) )' % (A1, E, E))
    lt2 = w.s([lt, bi], 'mpbid', '( %s -> ( T - ( T - 1 ) ) < ( T - %s ) )' % (A1, E))
    nc = w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % A1), a1(w, A1, 'ax-1cn', '1 e. CC')], 'nncand', '( %s -> ( T - ( T - 1 ) ) = 1 )' % A1)
    d['t1e'] = w.s([nc, lt2], 'eqbrtrrd', '( %s -> 1 < ( T - %s ) )' % (A1, E))
    d['cfbs'] = w.s([w.s([cfb, erp], 'jca', '( %s -> ( %s /\\ %s e. RR+ ) )' % (A1, CFB, E)), w.inst('dlogcfb')], 'syl', '( %s -> %s )' % (A1, CFBS))
    return d


def hpt(w, ante, Z, mz, tr):
    """( ante -> Z e. CC ), ( ante -> ( Re ` Z ) e. RR ), ( ante -> T < ( Re ` Z ) ) from mz: Z e. HP T, tr: T e. RR"""
    bi = w.s([tr, w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ T < ( Re ` %s ) ) ) )' % (ante, Z, D, Z, Z))
    both = w.s([mz, bi], 'mpbid', '( %s -> ( %s e. CC /\\ T < ( Re ` %s ) ) )' % (ante, Z, Z))
    zc = w.s([both], 'simpld', '( %s -> %s e. CC )' % (ante, Z))
    lt = w.s([both], 'simprd', '( %s -> T < ( Re ` %s ) )' % (ante, Z))
    rz = w.s([zc], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (ante, Z))
    return zc, rz, lt


def majv(w, ante, MJ, body_n, body_j, sub, mj):
    """( ante -> ( MJ ` j ) = body_j ) for a majorant mapping in n"""
    return mpv(w, ante, MJ, 'j', body_j, sub, mj, vexd(w, ante, body_j))


# ---------------------------------------------------------------- dsertdvb
w = W('dsertdvb', 'The termwise bound on the derivative series of a Dirichlet series on the half-plane, '
      'by shifting the abscissa half-way to the line one ( ~ dlogcfb , ~ dtmabs ).')
A0 = '( %s /\\ ( K e. NN /\\ Z e. %s ) )' % (HYP, D)
d = hypctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, HYP)))
kn = w.s([], 'simprl', '( %s -> K e. NN )' % A0)
zh = w.s([], 'simprr', '( %s -> Z e. %s )' % (A0, D))
zc, rz, lt = hpt(w, A0, 'Z', zh, d['tr'])
zme = w.s([zc, d['ec']], 'subcld', '( %s -> ( Z - %s ) e. CC )' % (A0, E))
rzme = w.s([w.s([zc, d['ec']], 'resubd', '( %s -> ( Re ` ( Z - %s ) ) = ( %s - ( Re ` %s ) ) )' % (A0, E, RZ, E)),
            w.s([w.s([d['er']], 'rered', '( %s -> ( Re ` %s ) = %s )' % (A0, E, E))], 'oveq2d',
                '( %s -> ( %s - ( Re ` %s ) ) = ( %s - %s ) )' % (A0, RZ, E, RZ, E))], 'eqtrd',
           '( %s -> ( Re ` ( Z - %s ) ) = ( %s - %s ) )' % (A0, E, RZ, E))
le = w.s([d['tr'], rz, d['er'], w.s([d['tr'], rz, lt], 'ltled', '( %s -> T <_ %s )' % (A0, RZ))], 'lesub1dd',
         '( %s -> ( T - %s ) <_ ( %s - %s ) )' % (A0, E, RZ, E))
le2 = w.s([le, w.s([rzme], 'eqcomd', '( %s -> ( %s - %s ) = ( Re ` ( Z - %s ) ) )' % (A0, RZ, E, E))], 'breqtrd',
          '( %s -> ( T - %s ) <_ ( Re ` ( Z - %s ) ) )' % (A0, E, E))
pack = w.s([d['cfbs'], w.s([w.s([kn, d['tme'], zme], '3jca', '( %s -> ( K e. NN /\\ ( T - %s ) e. RR /\\ ( Z - %s ) e. CC ) )' % (A0, E, E)), le2],
                           'jca', '( %s -> ( ( K e. NN /\\ ( T - %s ) e. RR /\\ ( Z - %s ) e. CC ) /\\ ( T - %s ) <_ ( Re ` ( Z - %s ) ) ) )' % (A0, E, E, E, E))],
           'jca', '( %s -> ( %s /\\ ( ( K e. NN /\\ ( T - %s ) e. RR /\\ ( Z - %s ) e. CC ) /\\ ( T - %s ) <_ ( Re ` ( Z - %s ) ) ) ) )' % (A0, CFBS, E, E, E, E))
BND = '( ( C / %s ) x. ( K ^c -u ( T - %s ) ) )' % (E, E)
bd = w.s([pack, w.inst('dtmabs')], 'syl', '( %s -> ( abs ` ( ( %s ` K ) x. ( K ^c -u ( Z - %s ) ) ) ) <_ %s )' % (A0, SHC, E, BND))
SHCK = '( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u %s ) )' % E
sv = w.s([kn, w.inst('dshcval')], 'syl', '( %s -> ( %s ` K ) = %s )' % (A0, SHC, SHCK))
BK = '( ( A ` K ) x. ( log ` K ) )'
bkc = w.s([w.s([d['af'], kn], 'ffvelcdmd', '( %s -> ( A ` K ) e. CC )' % A0),
           w.s([w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)], 'recnd',
               '( %s -> ( log ` K ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, BK))
tr = w.s([w.s([w.s([kn, d['ec'], zc], '3jca', '( %s -> ( K e. NN /\\ %s e. CC /\\ Z e. CC ) )' % (A0, E)), bkc], 'jca',
              '( %s -> ( ( K e. NN /\\ %s e. CC /\\ Z e. CC ) /\\ %s e. CC ) )' % (A0, E, BK)), w.inst('dlogtrm')], 'syl',
         '( %s -> ( %s x. ( K ^c -u ( Z - %s ) ) ) = %s )' % (A0, SHCK, E, LTRM('A', 'K', 'Z')))
eq = w.s([w.s([sv], 'oveq1d', '( %s -> ( ( %s ` K ) x. ( K ^c -u ( Z - %s ) ) ) = ( %s x. ( K ^c -u ( Z - %s ) ) ) )' % (A0, SHC, E, SHCK, E)), tr],
         'eqtrd', '( %s -> ( ( %s ` K ) x. ( K ^c -u ( Z - %s ) ) ) = %s )' % (A0, SHC, E, LTRM('A', 'K', 'Z')))
bd2 = w.s([w.s([eq], 'fveq2d', '( %s -> ( abs ` ( ( %s ` K ) x. ( K ^c -u ( Z - %s ) ) ) ) = ( abs ` %s ) )' % (A0, SHC, E, LTRM('A', 'K', 'Z'))), bd],
          'eqbrtrrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, LTRM('A', 'K', 'Z'), BND))
ltc = w.s([bkc, w.s([w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0), w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')], 'syl2anc',
                    '( %s -> ( K ^c -u Z ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, LTRM('A', 'K', 'Z')))
w.qed([w.s([ltc], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (A0, LTRM('A', 'K', 'Z'), LTRM('A', 'K', 'Z'))), bd2], 'eqbrtrd',
      '( %s -> ( abs ` -u %s ) <_ %s )' % (A0, LTRM('A', 'K', 'Z'), BND))
run5(w)

# ---------------------------------------------------------------- dseruh
w = W('dseruh', 'The term functions of a Dirichlet series with bounded coefficients on the half-plane '
      '` 1 < T ` satisfy the hypotheses of the uniform-limit theorem ~ uhhol .')
A0 = HYP
d = hypctx(w, A0)
UT = UHT(SQ, D)
sqf = w.s([d['af'], w.inst('dsqff')], 'syl', '( %s -> %s : NN --> ( CC ^m %s ) )' % (A0, SQ, D))
# termwise HOL
Aj = '( %s /\\ j e. NN )' % A0
jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
MPJ = '( p e. %s |-> %s )' % (D, TRM('A', 'j', 'p'))
sv = w.s([jn, w.inst('dsqfv')], 'syl', '( %s -> ( %s ` j ) = %s )' % (Aj, SQ, MPJ))
hol = w.s([w.s([w.s([d['af']], 'adantr', '( %s -> A : NN --> CC )' % Aj), jn], 'jca', '( %s -> ( A : NN --> CC /\\ j e. NN ) )' % Aj),
           w.inst('dserthol')], 'syl', '( %s -> %s )' % (Aj, HOLG2(MPJ, D)))
c1 = w.s([sv, w.s([hol], 'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Aj, MPJ, D))], 'eqeltrd', '( %s -> ( %s ` j ) e. ( %s -cn-> CC ) )' % (Aj, SQ, D))
dm = w.s([w.s([sv], 'oveq2d', '( %s -> ( CC _D ( %s ` j ) ) = ( CC _D %s ) )' % (Aj, SQ, MPJ))], 'dmeqd',
         '( %s -> dom ( CC _D ( %s ` j ) ) = dom ( CC _D %s ) )' % (Aj, SQ, MPJ))
c2 = w.s([w.s([hol], 'simprd', '( %s -> %s C_ dom ( CC _D %s ) )' % (Aj, D, MPJ)), dm], 'sseqtrrd', '( %s -> %s C_ dom ( CC _D ( %s ` j ) ) )' % (Aj, D, SQ))
ral = w.s([w.s([c1, c2], 'jca', '( %s -> %s )' % (Aj, HOLG2('( %s ` j )' % SQ, D)))], 'ralrimiva', '( %s -> %s )' % (A0, UT))
left = w.s([sqf, ral], 'jca', '( %s -> ( %s : NN --> ( CC ^m %s ) /\\ %s ) )' % (A0, SQ, D, UT))
# the majorant M
An = '( %s /\\ n e. NN )' % A0
nn = w.s([], 'simpr', '( %s -> n e. NN )' % An)
ntr = w.s([w.s([d['tr']], 'renegcld', '( %s -> -u T e. RR )' % A0)], 'adantr', '( %s -> -u T e. RR )' % An)
pw = w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An), ntr], 'rpcxpcld', '( %s -> ( n ^c -u T ) e. RR+ )' % An)], 'rpred',
         '( %s -> ( n ^c -u T ) e. RR )' % An)
mre = w.s([w.s([d['cr']], 'adantr', '( %s -> C e. RR )' % An), pw], 'remulcld', '( %s -> ( C x. ( n ^c -u T ) ) e. RR )' % An)
mf = w.s([mre, w.s([], 'eqid', '%s = %s' % (MAJ, MAJ))], 'fmptd', '( %s -> %s : NN --> RR )' % (A0, MAJ))
mcv = w.s([w.s([d['tt'], w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0)], 'jca', '( %s -> ( ( T e. RR /\\ 1 < T ) /\\ C e. CC ) )' % A0),
           w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAJ))
Ajy = '( %s /\\ ( j e. NN /\\ y e. %s ) )' % (A0, D)
jn2 = w.s([], 'simprl', '( %s -> j e. NN )' % Ajy)
yh = w.s([], 'simprr', '( %s -> y e. %s )' % (Ajy, D))
trj = w.s([d['tr']], 'adantr', '( %s -> T e. RR )' % Ajy)
yc, ry, lty = hpt(w, Ajy, 'y', yh, trj)
vv = w.s([w.s([jn2, yh], 'jca', '( %s -> ( j e. NN /\\ y e. %s ) )' % (Ajy, D)), w.inst('dsqfvv')], 'syl',
         '( %s -> ( ( %s ` j ) ` y ) = %s )' % (Ajy, SQ, TRM('A', 'j', 'y')))
pk = w.s([w.s([d['cfb']], 'adantr', '( %s -> %s )' % (Ajy, CFB)),
          w.s([w.s([jn2, trj, yc], '3jca', '( %s -> ( j e. NN /\\ T e. RR /\\ y e. CC ) )' % Ajy),
               w.s([trj, ry, lty], 'ltled', '( %s -> T <_ ( Re ` y ) )' % Ajy)], 'jca',
              '( %s -> ( ( j e. NN /\\ T e. RR /\\ y e. CC ) /\\ T <_ ( Re ` y ) ) )' % Ajy)], 'jca',
         '( %s -> ( %s /\\ ( ( j e. NN /\\ T e. RR /\\ y e. CC ) /\\ T <_ ( Re ` y ) ) ) )' % (Ajy, CFB))
bd = w.s([pk, w.inst('dtmabs')], 'syl', '( %s -> ( abs ` %s ) <_ ( C x. ( j ^c -u T ) ) )' % (Ajy, TRM('A', 'j', 'y')))
subm = w.s([w.s([], 'oveq1', '( n = j -> ( n ^c -u T ) = ( j ^c -u T ) )')], 'oveq2d', '( n = j -> ( C x. ( n ^c -u T ) ) = ( C x. ( j ^c -u T ) ) )')
mv = majv(w, Ajy, MAJ, None, '( C x. ( j ^c -u T ) )', subm, jn2)
bd2 = w.s([w.s([w.s([vv], 'fveq2d', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s ) )' % (Ajy, SQ, TRM('A', 'j', 'y'))), bd], 'eqbrtrd',
                '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( C x. ( j ^c -u T ) ) )' % (Ajy, SQ)), mv], 'breqtrrd',
          '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (Ajy, SQ, MAJ))
mb = w.s([bd2], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (A0, D, SQ, MAJ))
um = w.s([mf, mcv, mb], '3jca', '( %s -> %s )' % (A0, UHM(SQ, MAJ, D)))
# the majorant R
CE = '( C / %s )' % E
cer = w.s([d['cr'], d['erp']], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, CE))
ntme = w.s([w.s([d['tme']], 'renegcld', '( %s -> -u ( T - %s ) e. RR )' % (A0, E))], 'adantr', '( %s -> -u ( T - %s ) e. RR )' % (An, E))
pw2 = w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An), ntme], 'rpcxpcld', '( %s -> ( n ^c -u ( T - %s ) ) e. RR+ )' % (An, E))], 'rpred',
          '( %s -> ( n ^c -u ( T - %s ) ) e. RR )' % (An, E))
rre = w.s([w.s([cer], 'adantr', '( %s -> %s e. RR )' % (An, CE)), pw2], 'remulcld', '( %s -> ( %s x. ( n ^c -u ( T - %s ) ) ) e. RR )' % (An, CE, E))
rf = w.s([rre, w.s([], 'eqid', '%s = %s' % (MAJD, MAJD))], 'fmptd', '( %s -> %s : NN --> RR )' % (A0, MAJD))
rcv = w.s([w.s([w.s([d['tme'], d['t1e']], 'jca', '( %s -> ( ( T - %s ) e. RR /\\ 1 < ( T - %s ) ) )' % (A0, E, E)),
                w.s([cer], 'recnd', '( %s -> %s e. CC )' % (A0, CE))], 'jca',
               '( %s -> ( ( ( T - %s ) e. RR /\\ 1 < ( T - %s ) ) /\\ %s e. CC ) )' % (A0, E, E, CE)), w.inst('zsercvgc')], 'syl',
          '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAJD))
# the derivative bound
NLJ = '-u %s' % LTRM('A', 'j', 'p')
NLJY = '-u %s' % LTRM('A', 'j', 'y')
dvj = w.s([w.s([w.s([w.s([d['af']], 'adantr', '( %s -> A : NN --> CC )' % Ajy), jn2], 'jca', '( %s -> ( A : NN --> CC /\\ j e. NN ) )' % Ajy),
                w.inst('dsertdv')], 'syl', '( %s -> ( CC _D %s ) = ( p e. %s |-> %s ) )' % (Ajy, MPJ, D, NLJ))], 'idi',
          '( %s -> ( CC _D %s ) = ( p e. %s |-> %s ) )' % (Ajy, MPJ, D, NLJ))
svj = w.s([w.s([jn2, w.inst('dsqfv')], 'syl', '( %s -> ( %s ` j ) = %s )' % (Ajy, SQ, MPJ))], 'oveq2d',
          '( %s -> ( CC _D ( %s ` j ) ) = ( CC _D %s ) )' % (Ajy, SQ, MPJ))
dvsq = w.s([svj, dvj], 'eqtrd', '( %s -> ( CC _D ( %s ` j ) ) = ( p e. %s |-> %s ) )' % (Ajy, SQ, D, NLJ))
suby = w.s([w.s([w.s([w.s([], 'negeq', '( p = y -> -u p = -u y )')], 'oveq2d', '( p = y -> ( j ^c -u p ) = ( j ^c -u y ) )')], 'oveq2d',
                '( p = y -> %s = %s )' % (LTRM('A', 'j', 'p'), LTRM('A', 'j', 'y')))], 'negeqd', '( p = y -> %s = %s )' % (NLJ, NLJY))
dval = mpv(w, Ajy, '( p e. %s |-> %s )' % (D, NLJ), 'y', NLJY, suby, yh, vexd(w, Ajy, NLJY, 'neg'), D)
dvv = w.s([w.s([dvsq], 'fveq1d', '( %s -> ( ( CC _D ( %s ` j ) ) ` y ) = ( ( p e. %s |-> %s ) ` y ) )' % (Ajy, SQ, D, NLJ)), dval], 'eqtrd',
          '( %s -> ( ( CC _D ( %s ` j ) ) ` y ) = %s )' % (Ajy, SQ, NLJY))
BNDJ = '( %s x. ( j ^c -u ( T - %s ) ) )' % (CE, E)
tb = w.s([w.s([w.s([d['hyp']], 'adantr', '( %s -> %s )' % (Ajy, HYP)), w.s([jn2, yh], 'jca', '( %s -> ( j e. NN /\\ y e. %s ) )' % (Ajy, D))], 'jca',
              '( %s -> ( %s /\\ ( j e. NN /\\ y e. %s ) ) )' % (Ajy, HYP, D)), w.inst('dsertdvb')], 'syl',
         '( %s -> ( abs ` %s ) <_ %s )' % (Ajy, NLJY, BNDJ))
subr = w.s([w.s([], 'oveq1', '( n = j -> ( n ^c -u ( T - %s ) ) = ( j ^c -u ( T - %s ) ) )' % (E, E))], 'oveq2d',
           '( n = j -> ( %s x. ( n ^c -u ( T - %s ) ) ) = %s )' % (CE, E, BNDJ))
rv = majv(w, Ajy, MAJD, None, BNDJ, subr, jn2)
db2 = w.s([w.s([w.s([dvv], 'fveq2d', '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) = ( abs ` %s ) )' % (Ajy, SQ, NLJY)), tb], 'eqbrtrd',
                '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ %s )' % (Ajy, SQ, BNDJ)), rv], 'breqtrrd',
          '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (Ajy, SQ, MAJD))
rb = w.s([db2], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (A0, D, SQ, MAJD))
ud = w.s([rf, rcv, rb], '3jca', '( %s -> %s )' % (A0, UHD(SQ, MAJD, D)))
w.qed([left, w.s([um, ud], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, UHM(SQ, MAJ, D), UHD(SQ, MAJD, D)))], 'jca',
      '( %s -> %s )' % (A0, UH(SQ, MAJ, MAJD, D)))
run5(w)

# ---------------------------------------------------------------- dsergeq
GS = GSUM(SQ, D)
w = W('dsergeq', 'The sum function of the Dirichlet term functions is the Dirichlet series as a function of the point.')
Azk = '( z e. %s /\\ k e. NN )' % D
vv = w.s([w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Azk), w.s([], 'simpl', '( %s -> z e. %s )' % (Azk, D))], 'jca',
              '( %s -> ( k e. NN /\\ z e. %s ) )' % (Azk, D)), w.inst('dsqfvv')], 'syl', '( %s -> ( ( %s ` k ) ` z ) = %s )' % (Azk, SQ, TRMZ('k')))
sm = w.s([vv], 'sumeq2dv', '( z e. %s -> sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN %s )' % (D, SQ, TRMZ('k')))
w.qed([sm], 'mpteq2ia', '%s = %s' % (GS, LSF()))
run5(w)

# ---------------------------------------------------------------- dserhol
w = W('dserhol', 'A Dirichlet series with bounded coefficients is holomorphic on every open half-plane '
      '` ( Re ` z ) > T ` with ` 1 < T ` : C2\'s ` HOL ` for the sum function ( ~ uhhol ).')
A0 = HYP
hol = w.s([w.s([], 'dseruh', '( %s -> %s )' % (A0, UH(SQ, MAJ, MAJD, D))), w.inst('uhhol')], 'syl', '( %s -> %s )' % (A0, HOLG2(GS, D)))
ge = w.s([], 'dsergeq', '%s = %s' % (GS, LSF()))
b1 = w.s([ge], 'eleq1i', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (GS, D, LSF(), D))
b2 = w.s([w.s([w.s([ge], 'oveq2i', '( CC _D %s ) = ( CC _D %s )' % (GS, LSF()))], 'dmeqi', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (GS, LSF()))],
         'sseq2i', '( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) )' % (D, GS, D, LSF()))
bi = w.s([b1, b2], 'anbi12i', '( %s <-> %s )' % (HOLG2(GS, D), HOLG2(LSF(), D)))
w.qed([hol, bi], 'sylib', '( %s -> %s )' % (A0, HOLG2(LSF(), D)))
run5(w)

# ---------------------------------------------------------------- dserdv
HS = HSUM(SQ, D)
w = W('dserdv', 'The derivative of a Dirichlet series on the half-plane is the series of the termwise '
      'derivatives ( ~ uhdv ): Mathlib\'s ` LSeries_deriv ` in function form.')
A0 = HYP
d = hypctx(w, A0)
dv = w.s([w.s([], 'dseruh', '( %s -> %s )' % (A0, UH(SQ, MAJ, MAJD, D))), w.inst('uhdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, GS, HS))
ge = w.s([w.s([w.s([], 'dsergeq', '%s = %s' % (GS, LSF()))], 'oveq2i', '( CC _D %s ) = ( CC _D %s )' % (GS, LSF()))], 'a1i',
         '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, GS, LSF()))
Az = '( %s /\\ z e. %s )' % (A0, D)
Azk = '( %s /\\ k e. NN )' % Az
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Azk)
zh = w.s([], 'simplr', '( %s -> z e. %s )' % (Azk, D))
MPK = '( p e. %s |-> %s )' % (D, TRM('A', 'k', 'p'))
NLK = '-u %s' % LTRM('A', 'k', 'p')
NLKZ = '-u %s' % LTRM('A', 'k', 'z')
dvk = w.s([w.s([w.s([d['af']], 'ad2antrr', '( %s -> A : NN --> CC )' % Azk), kn], 'jca', '( %s -> ( A : NN --> CC /\\ k e. NN ) )' % Azk),
           w.inst('dsertdv')], 'syl', '( %s -> ( CC _D %s ) = ( p e. %s |-> %s ) )' % (Azk, MPK, D, NLK))
svk = w.s([w.s([kn, w.inst('dsqfv')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Azk, SQ, MPK))], 'oveq2d',
          '( %s -> ( CC _D ( %s ` k ) ) = ( CC _D %s ) )' % (Azk, SQ, MPK))
dsq = w.s([svk, dvk], 'eqtrd', '( %s -> ( CC _D ( %s ` k ) ) = ( p e. %s |-> %s ) )' % (Azk, SQ, D, NLK))
subz = w.s([w.s([w.s([w.s([], 'negeq', '( p = z -> -u p = -u z )')], 'oveq2d', '( p = z -> ( k ^c -u p ) = ( k ^c -u z ) )')], 'oveq2d',
                '( p = z -> %s = %s )' % (LTRM('A', 'k', 'p'), LTRM('A', 'k', 'z')))], 'negeqd', '( p = z -> %s = %s )' % (NLK, NLKZ))
val = mpv(w, Azk, '( p e. %s |-> %s )' % (D, NLK), 'z', NLKZ, subz, zh, vexd(w, Azk, NLKZ, 'neg'), D)
tv = w.s([w.s([dsq], 'fveq1d', '( %s -> ( ( CC _D ( %s ` k ) ) ` z ) = ( ( p e. %s |-> %s ) ` z ) )' % (Azk, SQ, D, NLK)), val], 'eqtrd',
         '( %s -> ( ( CC _D ( %s ` k ) ) ` z ) = %s )' % (Azk, SQ, NLKZ))
NLK = NLKZ
sm = w.s([tv], 'sumeq2dv', '( %s -> sum_ k e. NN ( ( CC _D ( %s ` k ) ) ` z ) = sum_ k e. NN %s )' % (Az, SQ, NLK))
hd = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A0, HS, DSF()))
w.qed([w.s([dv, ge], 'eqtr3d', '( %s -> %s = ( CC _D %s ) )' % (A0, HS, LSF())), hd], 'eqtr3d',
      '( %s -> ( CC _D %s ) = %s )' % (A0, LSF(), DSF()))
run5(w)
