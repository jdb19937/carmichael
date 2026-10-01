"""C5, Dirichlet instance 1: the term functions of a Dirichlet series on a
half-plane, their values, their derivative and their holomorphy."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

D = HP()
SQ = SQF()


def TRMZ(K, z='z'):
    return TRM('A', K, z)


def hpex(w, ante):
    """( ante -> HP T e. _V )"""
    e = w.s([w.s([], 'cnex', 'CC e. _V'), w.s([], 'hpss', '%s C_ CC' % D)], 'ssexi', '%s e. _V' % D)
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, D))





def trmcl(w, ante, K, Z, af, mk, mz):
    """( ante -> TRM(K,Z) e. CC ) from af: A : NN --> CC, mk: K e. NN, mz: Z e. HP T"""
    ak = w.s([af, mk], 'ffvelcdmd', '( %s -> ( A ` %s ) e. CC )' % (ante, K))
    zc = w.s([a1(w, ante, 'hpss', '%s C_ CC' % D), mz], 'sseldd', '( %s -> %s e. CC )' % (ante, Z))
    pw = w.s([w.s([mk], 'nncnd', '( %s -> %s e. CC )' % (ante, K)), w.s([zc], 'negcld', '( %s -> -u %s e. CC )' % (ante, Z)),
              w.inst('cxpcl')], 'syl2anc', '( %s -> ( %s ^c -u %s ) e. CC )' % (ante, K, Z))
    return w.s([ak, pw], 'mulcld', '( %s -> %s e. CC )' % (ante, TRM('A', K, Z))), ak, zc, pw


# ---------------------------------------------------------------- cxpnegdv
w = W('cxpnegdv', 'The derivative of ` ( K ^c -u z ) ` on an open set ( ~ dvcxp2 , ~ dvmptco ).')
A0 = '( K e. RR+ /\\ U e. %s )' % TOP
krp = w.s([], 'simpl', '( %s -> K e. RR+ )' % A0)
uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, TOP))
kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0)
lk = w.s([w.s([krp], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)], 'recnd', '( %s -> ( log ` K ) e. CC )' % A0)
sc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
Az = '( %s /\\ z e. CC )' % A0
zc = w.s([], 'simpr', '( %s -> z e. CC )' % Az)
nz = w.s([zc], 'negcld', '( %s -> -u z e. CC )' % Az)
m1 = a1(w, Az, 'neg1cn', '-u 1 e. CC')
one = a1(w, Az, 'ax-1cn', '1 e. CC')
Ay = '( %s /\\ y e. CC )' % A0
yc = w.s([], 'simpr', '( %s -> y e. CC )' % Ay)
ky = w.s([w.s([kc], 'adantr', '( %s -> K e. CC )' % Ay), yc, w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c y ) e. CC )' % Ay)
lky = w.s([w.s([lk], 'adantr', '( %s -> ( log ` K ) e. CC )' % Ay), ky], 'mulcld', '( %s -> ( ( log ` K ) x. ( K ^c y ) ) e. CC )' % Ay)
did = w.s([sc], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)
dneg = w.s([sc, zc, one, did], 'dvmptneg', '( %s -> ( CC _D ( z e. CC |-> -u z ) ) = ( z e. CC |-> -u 1 ) )' % A0)
dcx = w.s([krp, w.inst('dvcxp2')], 'syl', '( %s -> ( CC _D ( y e. CC |-> ( K ^c y ) ) ) = ( y e. CC |-> ( ( log ` K ) x. ( K ^c y ) ) ) )' % A0)
se = w.s([], 'oveq2', '( y = -u z -> ( K ^c y ) = ( K ^c -u z ) )')
sf = w.s([se], 'oveq2d', '( y = -u z -> ( ( log ` K ) x. ( K ^c y ) ) = ( ( log ` K ) x. ( K ^c -u z ) ) )')
BODY = '( ( ( log ` K ) x. ( K ^c -u z ) ) x. -u 1 )'
dco = w.s([sc, sc, nz, m1, ky, lky, dneg, dcx, se, sf], 'dvmptco',
          '( %s -> ( CC _D ( z e. CC |-> ( K ^c -u z ) ) ) = ( z e. CC |-> %s ) )' % (A0, BODY))
# restrict to U
kz = w.s([w.s([kc], 'adantr', '( %s -> K e. CC )' % Az), nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u z ) e. CC )' % Az)
lkz = w.s([w.s([lk], 'adantr', '( %s -> ( log ` K ) e. CC )' % Az), kz], 'mulcld', '( %s -> ( ( log ` K ) x. ( K ^c -u z ) ) e. CC )' % Az)
bc = w.s([lkz, m1], 'mulcld', '( %s -> %s e. CC )' % (Az, BODY))
ucc = opnss(w, A0, uo)
ej = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
dres = w.s([sc, kz, bc, dco, ucc, ej, ek, uo], 'dvmptres', '( %s -> ( CC _D ( z e. U |-> ( K ^c -u z ) ) ) = ( z e. U |-> %s ) )' % (A0, BODY))
Au = '( %s /\\ z e. U )' % A0
zcu = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Au), w.s([], 'simpr', '( %s -> z e. U )' % Au)], 'sseldd', '( %s -> z e. CC )' % Au)
kzu = w.s([w.s([kc], 'adantr', '( %s -> K e. CC )' % Au), w.s([zcu], 'negcld', '( %s -> -u z e. CC )' % Au), w.inst('cxpcl')], 'syl2anc',
          '( %s -> ( K ^c -u z ) e. CC )' % Au)
lkzu = w.s([w.s([lk], 'adantr', '( %s -> ( log ` K ) e. CC )' % Au), kzu], 'mulcld', '( %s -> ( ( log ` K ) x. ( K ^c -u z ) ) e. CC )' % Au)
sim = w.s([w.s([lkzu, a1(w, Au, 'neg1cn', '-u 1 e. CC')], 'mulcomd', '( %s -> %s = ( -u 1 x. ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % (Au, BODY)),
           w.s([lkzu], 'mulm1d', '( %s -> ( -u 1 x. ( ( log ` K ) x. ( K ^c -u z ) ) ) = -u ( ( log ` K ) x. ( K ^c -u z ) ) )' % Au)],
          'eqtrd', '( %s -> %s = -u ( ( log ` K ) x. ( K ^c -u z ) ) )' % (Au, BODY))
w.qed([dres, w.s([sim], 'mpteq2dva', '( %s -> ( z e. U |-> %s ) = ( z e. U |-> -u ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % (A0, BODY))],
      'eqtrd', '( %s -> ( CC _D ( z e. U |-> ( K ^c -u z ) ) ) = ( z e. U |-> -u ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % A0)
run5(w)

# ---------------------------------------------------------------- dsqfv
MPK = lambda K: '( p e. %s |-> %s )' % (D, TRM('A', K, 'p'))
w = W('dsqfv', 'The K-th term function of a Dirichlet series on a half-plane.')
s1 = w.s([w.s([], 'fveq2', '( a = K -> ( A ` a ) = ( A ` K ) )'), w.s([], 'oveq1', '( a = K -> ( a ^c -u p ) = ( K ^c -u p ) )')],
         'oveq12d', '( a = K -> %s = %s )' % (TRM('A', 'a', 'p'), TRM('A', 'K', 'p')))
s2 = w.s([s1], 'mpteq2dv', '( a = K -> %s = %s )' % (MPK('a'), MPK('K')))
eq = w.s([], 'eqid', '%s = %s' % (SQ, SQ))
hpe = w.s([w.s([], 'cnex', 'CC e. _V'), w.s([], 'hpss', '%s C_ CC' % D)], 'ssexi', '%s e. _V' % D)
ex = w.s([hpe], 'mptex', '%s e. _V' % MPK('K'))
w.qed([s2, eq, ex], 'fvmpt', '( K e. NN -> ( %s ` K ) = %s )' % (SQ, MPK('K')))
run5(w)

# ---------------------------------------------------------------- dsqfvv
w = W('dsqfvv', 'The value of a term function of a Dirichlet series at a point of the half-plane.')
A0 = '( K e. NN /\\ Z e. %s )' % D
kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
zh = w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, D))
fv = w.s([w.s([kn, w.inst('dsqfv')], 'syl', '( %s -> ( %s ` K ) = %s )' % (A0, SQ, MPK('K')))], 'fveq1d',
         '( %s -> ( ( %s ` K ) ` Z ) = ( %s ` Z ) )' % (A0, SQ, MPK('K')))
sub = w.s([w.s([w.s([], 'negeq', '( p = Z -> -u p = -u Z )')], 'oveq2d', '( p = Z -> ( K ^c -u p ) = ( K ^c -u Z ) )')], 'oveq2d',
          '( p = Z -> %s = %s )' % (TRM('A', 'K', 'p'), TRM('A', 'K', 'Z')))
val = mpv(w, A0, MPK('K'), 'Z', TRM('A', 'K', 'Z'), sub, zh, vexd(w, A0, TRM('A', 'K', 'Z')), D)
w.qed([fv, val], 'eqtrd', '( %s -> ( ( %s ` K ) ` Z ) = %s )' % (A0, SQ, TRM('A', 'K', 'Z')))
run5(w)

# ---------------------------------------------------------------- dsqff
w = W('dsqff', 'The term functions of a Dirichlet series form a sequence of functions on the half-plane.')
A0 = 'A : NN --> CC'
Ah = '( %s /\\ a e. NN )' % A0
Ahz = '( %s /\\ p e. %s )' % (Ah, D)
tc = trmcl(w, Ahz, 'a', 'p', w.s([], 'ad2antrr', '( %s -> A : NN --> CC )' % Ahz), w.s([], 'simplr', '( %s -> a e. NN )' % Ahz),
           w.s([], 'simpr', '( %s -> p e. %s )' % (Ahz, D)))[0]
mf = w.s([tc, w.s([], 'eqid', '%s = %s' % (MPK('a'), MPK('a')))], 'fmptd', '( %s -> %s : %s --> CC )' % (Ah, MPK('a'), D))
mm = elmapf(w, Ah, MPK('a'), hpex(w, Ah), mf, D)
w.qed([mm, w.s([], 'eqid', '%s = %s' % (SQ, SQ))], 'fmptd', '( %s -> %s : NN --> ( CC ^m %s ) )' % (A0, SQ, D))
run5(w)

# ---------------------------------------------------------------- dsertdv
w = W('dsertdv', 'The derivative of a term function of a Dirichlet series on the half-plane.')
A0 = '( A : NN --> CC /\\ K e. NN )'
af = w.s([], 'simpl', '( %s -> A : NN --> CC )' % A0)
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
ak = w.s([af, kn], 'ffvelcdmd', '( %s -> ( A ` K ) e. CC )' % A0)
sc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
Az = '( %s /\\ z e. %s )' % (A0, D)
zc = w.s([a1(w, Az, 'hpss', '%s C_ CC' % D), w.s([], 'simpr', '( %s -> z e. %s )' % (Az, D))], 'sseldd', '( %s -> z e. CC )' % Az)
kz = w.s([w.s([w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0)], 'adantr', '( %s -> K e. CC )' % Az), w.s([zc], 'negcld', '( %s -> -u z e. CC )' % Az),
          w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u z ) e. CC )' % Az)
lk = w.s([w.s([w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)], 'recnd',
              '( %s -> ( log ` K ) e. CC )' % A0)], 'adantr', '( %s -> ( log ` K ) e. CC )' % Az)
lkz = w.s([lk, kz], 'mulcld', '( %s -> ( ( log ` K ) x. ( K ^c -u z ) ) e. CC )' % Az)
nb = w.s([lkz], 'negcld', '( %s -> -u ( ( log ` K ) x. ( K ^c -u z ) ) e. CC )' % Az)
dv0 = w.s([w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0), a1(w, A0, 'hpopn', '%s e. %s' % (D, TOP))], 'jca',
                '( %s -> ( K e. RR+ /\\ %s e. %s ) )' % (A0, D, TOP)), w.inst('cxpnegdv')], 'syl',
          '( %s -> ( CC _D ( z e. %s |-> ( K ^c -u z ) ) ) = ( z e. %s |-> -u ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % (A0, D, D))
dcm = w.s([sc, kz, nb, dv0, ak], 'dvmptcmul',
          '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> ( ( A ` K ) x. -u ( ( log ` K ) x. ( K ^c -u z ) ) ) ) )' % (A0, D, TRMZ('K'), D))
akz = w.s([ak], 'adantr', '( %s -> ( A ` K ) e. CC )' % Az)
s1 = w.s([akz, lkz], 'mulneg2d', '( %s -> ( ( A ` K ) x. -u ( ( log ` K ) x. ( K ^c -u z ) ) ) = -u ( ( A ` K ) x. ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % Az)
s2 = w.s([w.s([w.s([akz, lk, kz], 'mulassd', '( %s -> ( ( ( A ` K ) x. ( log ` K ) ) x. ( K ^c -u z ) ) = ( ( A ` K ) x. ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % Az)],
              'eqcomd', '( %s -> ( ( A ` K ) x. ( ( log ` K ) x. ( K ^c -u z ) ) ) = %s )' % (Az, LTRM('A', 'K', 'z')))], 'negeqd',
         '( %s -> -u ( ( A ` K ) x. ( ( log ` K ) x. ( K ^c -u z ) ) ) = -u %s )' % (Az, LTRM('A', 'K', 'z')))
body = w.s([s1, s2], 'eqtrd', '( %s -> ( ( A ` K ) x. -u ( ( log ` K ) x. ( K ^c -u z ) ) ) = -u %s )' % (Az, LTRM('A', 'K', 'z')))
w.qed([dcm, w.s([body], 'mpteq2dva', '( %s -> ( z e. %s |-> ( ( A ` K ) x. -u ( ( log ` K ) x. ( K ^c -u z ) ) ) ) = ( z e. %s |-> -u %s ) )' % (A0, D, D, LTRM('A', 'K', 'z')))],
      'eqtrd', '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> -u %s ) )' % (A0, D, TRMZ('K'), D, LTRM('A', 'K', 'z')))
run5(w)

# ---------------------------------------------------------------- dserthol
w = W('dserthol', 'A term function of a Dirichlet series is holomorphic on the half-plane.')
A0 = '( A : NN --> CC /\\ K e. NN )'
MPK = '( z e. %s |-> %s )' % (D, TRMZ('K'))
NL = '-u %s' % LTRM('A', 'K', 'z')
af = w.s([], 'simpl', '( %s -> A : NN --> CC )' % A0)
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
Az = '( %s /\\ z e. %s )' % (A0, D)
tc, ak, zc, pw = trmcl(w, Az, 'K', 'z', w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Az), w.s([kn], 'adantr', '( %s -> K e. NN )' % Az),
                       w.s([], 'simpr', '( %s -> z e. %s )' % (Az, D)))
lk = w.s([w.s([w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)], 'recnd',
              '( %s -> ( log ` K ) e. CC )' % A0)], 'adantr', '( %s -> ( log ` K ) e. CC )' % Az)
cls = w.s([w.s([w.s([ak, lk], 'mulcld', '( %s -> ( ( A ` K ) x. ( log ` K ) ) e. CC )' % Az), pw], 'mulcld',
                '( %s -> %s e. CC )' % (Az, LTRM('A', 'K', 'z')))], 'negcld', '( %s -> %s e. CC )' % (Az, NL))
dveq = w.s([], 'dsertdv', '( %s -> ( CC _D %s ) = ( z e. %s |-> %s ) )' % (A0, MPK, D, NL))
ssd = dvdom(w, A0, MPK, 'z', D, NL, dveq, cls)
hf = w.s([cls, w.s([], 'eqid', '( z e. %s |-> %s ) = ( z e. %s |-> %s )' % (D, NL, D, NL))], 'fmptd', '( %s -> ( z e. %s |-> %s ) : %s --> CC )' % (A0, D, NL, D))
dm = w.s([w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( z e. %s |-> %s ) )' % (A0, MPK, D, NL)),
          w.s([hf, w.inst('fdm')], 'syl', '( %s -> dom ( z e. %s |-> %s ) = %s )' % (A0, D, NL, D))], 'eqtrd', '( %s -> dom ( CC _D %s ) = %s )' % (A0, MPK, D))
gf = w.s([tc, w.s([], 'eqid', '%s = %s' % (MPK, MPK))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, MPK, D))
cn = w.s([w.s([w.s([a1(w, A0, 'ssid', 'CC C_ CC'), gf, a1(w, A0, 'hpss', '%s C_ CC' % D)], '3jca',
                   '( %s -> ( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC ) )' % (A0, MPK, D, D)), dm], 'jca',
              '( %s -> ( ( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC ) /\\ dom ( CC _D %s ) = %s ) )' % (A0, MPK, D, D, MPK, D)), w.inst('dvcn')],
         'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, MPK, D))
w.qed([cn, ssd], 'jca', '( %s -> %s )' % (A0, HOLG2(MPK, D)))
run5(w)
