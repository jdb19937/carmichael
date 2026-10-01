"""C4, Abel block 2: the Abel series on the right half-plane."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import num

RZ = '( Re ` Z )'
T1 = '( %s + 1 )' % RZ
DIF = '( ( K ^c -u Z ) - ( ( K + 1 ) ^c -u Z ) )'

# ---------------------------------------------------------------- abtmbnd
A0 = '( ( S e. CC /\\ B e. RR /\\ ( abs ` S ) <_ B ) /\\ ( K e. NN /\\ Z e. CC /\\ 0 < %s ) )' % RZ
w = W('abtmbnd', 'The Abel term bound: a bounded partial sum against the difference '
      'of two consecutive powers.  The analytic content is the mean-value bound '
      '~ cxpmvt .')
sc = w.s([], 'simpl1', '( %s -> S e. CC )' % A0)
br = w.s([], 'simpl2', '( %s -> B e. RR )' % A0)
sb = w.s([], 'simpl3', '( %s -> ( abs ` S ) <_ B )' % A0)
kn = w.s([], 'simpr1', '( %s -> K e. NN )' % A0)
zc = w.s([], 'simpr2', '( %s -> Z e. CC )' % A0)
z0 = w.s([], 'simpr3', '( %s -> 0 < %s )' % (A0, RZ))
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0)
nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0)
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
one = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
t1r = w.s([rzr, one], 'readdcld', '( %s -> %s e. RR )' % (A0, T1))
nt1 = w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (A0, T1))
mvt = w.s([w.s([kn, zc], 'jca', '( %s -> ( K e. NN /\\ Z e. CC ) )' % A0), z0, w.inst('cxpmvt')], 'syl2anc',
          '( %s -> ( abs ` %s ) <_ ( ( abs ` Z ) x. ( K ^c ( -u %s - 1 ) ) ) )' % (A0, DIF, RZ))
# ( -u ( Re ` Z ) - 1 ) = -u ( ( Re ` Z ) + 1 )
neg = w.s([w.s([rzr], 'recnd', '( %s -> %s e. CC )' % (A0, RZ)),
           w.s([one], 'recnd', '( %s -> 1 e. CC )' % A0)], 'negdi2d',
          '( %s -> -u ( %s + 1 ) = ( -u %s - 1 ) )' % (A0, RZ, RZ))
mvt2 = w.s([mvt, w.s([w.s([w.s([neg], 'eqcomd', '( %s -> ( -u %s - 1 ) = -u %s )' % (A0, RZ, T1))], 'oveq2d',
                          '( %s -> ( K ^c ( -u %s - 1 ) ) = ( K ^c -u %s ) )' % (A0, RZ, T1))], 'oveq2d',
                     '( %s -> ( ( abs ` Z ) x. ( K ^c ( -u %s - 1 ) ) ) = ( ( abs ` Z ) x. ( K ^c -u %s ) ) )' % (A0, RZ, T1))], 'breqtrd',
           '( %s -> ( abs ` %s ) <_ ( ( abs ` Z ) x. ( K ^c -u %s ) ) )' % (A0, DIF, T1))
# assemble
dcl = w.s([w.s([kc, nzc], 'cxpcld', '( %s -> ( K ^c -u Z ) e. CC )' % A0),
           w.s([w.s([w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)], 'nncnd',
                    '( %s -> ( K + 1 ) e. CC )' % A0), nzc], 'cxpcld', '( %s -> ( ( K + 1 ) ^c -u Z ) e. CC )' % A0)],
          'subcld', '( %s -> %s e. CC )' % (A0, DIF))
am = w.s([sc, dcl], 'absmuld', '( %s -> ( abs ` ( S x. %s ) ) = ( ( abs ` S ) x. ( abs ` %s ) ) )' % (A0, DIF, DIF))
azr = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
kp = w.s([krp, nt1], 'rpcxpcld', '( %s -> ( K ^c -u %s ) e. RR+ )' % (A0, T1))
rhs = w.s([azr, w.s([kp], 'rpred', '( %s -> ( K ^c -u %s ) e. RR )' % (A0, T1))], 'remulcld',
          '( %s -> ( ( abs ` Z ) x. ( K ^c -u %s ) ) e. RR )' % (A0, T1))
mul = w.s([w.s([sc], 'abscld', '( %s -> ( abs ` S ) e. RR )' % A0), br,
           w.s([dcl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, DIF)), rhs,
           w.s([sc], 'absge0d', '( %s -> 0 <_ ( abs ` S ) )' % A0),
           w.s([dcl], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, DIF)), sb, mvt2], 'lemul12ad',
          '( %s -> ( ( abs ` S ) x. ( abs ` %s ) ) <_ ( B x. ( ( abs ` Z ) x. ( K ^c -u %s ) ) ) )' % (A0, DIF, T1))
ass = w.s([w.s([br], 'recnd', '( %s -> B e. CC )' % A0), w.s([azr], 'recnd', '( %s -> ( abs ` Z ) e. CC )' % A0),
           w.s([kp], 'rpcnd', '( %s -> ( K ^c -u %s ) e. CC )' % (A0, T1))], 'mulassd',
          '( %s -> ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) = ( B x. ( ( abs ` Z ) x. ( K ^c -u %s ) ) ) )' % (A0, T1, T1))
w.qed([am, w.s([mul, w.s([ass], 'eqcomd',
                         '( %s -> ( B x. ( ( abs ` Z ) x. ( K ^c -u %s ) ) ) = ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) )' % (A0, T1, T1))],
               'breqtrd', '( %s -> ( ( abs ` S ) x. ( abs ` %s ) ) <_ ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) )' % (A0, DIF, T1))],
      'eqbrtrd', '( %s -> ( abs ` ( S x. %s ) ) <_ ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) )' % (A0, DIF, T1))
run4(w)

# ---------------------------------------------------------------- abcfb
def ATMV(k):
    return '( ( S ` %s ) x. ( ( %s ^c -u Z ) - ( ( %s + 1 ) ^c -u Z ) ) )' % (k, k, k)


AA = '( q e. NN |-> ( %s x. ( q ^c %s ) ) )' % (ATMV('q'), T1)
ABS = '( S : NN --> CC /\\ B e. RR /\\ A. m e. NN ( abs ` ( S ` m ) ) <_ B )'
ZPP = '( Z e. CC /\\ 0 < %s )' % RZ
A1 = '( %s /\\ %s )' % (ABS, ZPP)
BZ = '( B x. ( abs ` Z ) )'
w = W('abcfb', 'The Abel coefficients, normalised by ` ( k ^c ( ( Re ` Z ) + 1 ) ) `, '
      'satisfy the bounded-coefficient interface of ~ dserbnd at the abscissa '
      '` ( ( Re ` Z ) + 1 ) `.')
sf = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ABS)), w.inst('simp1')], 'syl', '( %s -> S : NN --> CC )' % A1)
br = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ABS)), w.inst('simp2')], 'syl', '( %s -> B e. RR )' % A1)
sall = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ABS)), w.inst('simp3')], 'syl',
           '( %s -> A. m e. NN ( abs ` ( S ` m ) ) <_ B )' % A1)
zc = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, ZPP)), w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A1)
z0 = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, ZPP)), w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (A1, RZ))
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A1, RZ))
one = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A1)
t1r = w.s([rzr, one], 'readdcld', '( %s -> %s e. RR )' % (A1, T1))
azr = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A1)
bzr = w.s([br, azr], 'remulcld', '( %s -> %s e. RR )' % (A1, BZ))
def cls(v):
    """the closure steps for the AA body at the letter v, under ( A1 /\\ v e. NN )"""
    AV = '( %s /\\ %s e. NN )' % (A1, v)
    vn = w.s([], 'simpr', '( %s -> %s e. NN )' % (AV, v))
    vrp = w.s([vn], 'nnrpd', '( %s -> %s e. RR+ )' % (AV, v))
    vc = w.s([vrp], 'rpcnd', '( %s -> %s e. CC )' % (AV, v))
    nzd = w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % AV)], 'negcld', '( %s -> -u Z e. CC )' % AV)
    t1d = w.s([t1r], 'adantr', '( %s -> %s e. RR )' % (AV, T1))
    scl = w.s([w.s([sf], 'adantr', '( %s -> S : NN --> CC )' % AV), vn], 'ffvelcdmd',
              '( %s -> ( S ` %s ) e. CC )' % (AV, v))
    v1c = w.s([w.s([w.s([vn, w.inst('peano2nn')], 'syl', '( %s -> ( %s + 1 ) e. NN )' % (AV, v))], 'nncnd',
                   '( %s -> ( %s + 1 ) e. CC )' % (AV, v)), nzd], 'cxpcld',
              '( %s -> ( ( %s + 1 ) ^c -u Z ) e. CC )' % (AV, v))
    difc = w.s([w.s([vc, nzd], 'cxpcld', '( %s -> ( %s ^c -u Z ) e. CC )' % (AV, v)), v1c], 'subcld',
               '( %s -> ( ( %s ^c -u Z ) - ( ( %s + 1 ) ^c -u Z ) ) e. CC )' % (AV, v, v))
    atc = w.s([scl, difc], 'mulcld', '( %s -> %s e. CC )' % (AV, ATMV(v)))
    vt1 = w.s([vrp, t1d], 'rpcxpcld', '( %s -> ( %s ^c %s ) e. RR+ )' % (AV, v, T1))
    vcl = w.s([atc, w.s([vt1], 'rpcnd', '( %s -> ( %s ^c %s ) e. CC )' % (AV, v, T1))], 'mulcld',
              '( %s -> ( %s x. ( %s ^c %s ) ) e. CC )' % (AV, ATMV(v), v, T1))
    return AV, vn, vrp, vc, nzd, t1d, scl, difc, atc, vt1, vcl


AQ, qn, qrp, qc, nzq, t1q, sclq, difq, atq, qt1, vclq = cls('q')
fn = w.s([vclq, w.s([], 'eqid', '%s = %s' % (AA, AA))], 'fmptd', '( %s -> %s : NN --> CC )' % (A1, AA))
AD, dn, drp, dc, nzd, t1d, scl, difc, atc, dt1, vcl = cls('d')
# the value of AA at d
sub = w.s([w.s([w.s([], 'fveq2', '( q = d -> ( S ` q ) = ( S ` d ) )'),
                w.s([w.s([], 'oveq1', '( q = d -> ( q ^c -u Z ) = ( d ^c -u Z ) )'),
                     w.s([w.s([], 'oveq1', '( q = d -> ( q + 1 ) = ( d + 1 ) )')], 'oveq1d',
                         '( q = d -> ( ( q + 1 ) ^c -u Z ) = ( ( d + 1 ) ^c -u Z ) )')], 'oveq12d',
                    '( q = d -> ( ( q ^c -u Z ) - ( ( q + 1 ) ^c -u Z ) ) = ( ( d ^c -u Z ) - ( ( d + 1 ) ^c -u Z ) ) )')],
               'oveq12d', '( q = d -> %s = %s )' % (ATMV('q'), ATMV('d'))),
           w.s([], 'oveq1', '( q = d -> ( q ^c %s ) = ( d ^c %s ) )' % (T1, T1))], 'oveq12d',
          '( q = d -> ( %s x. ( q ^c %s ) ) = ( %s x. ( d ^c %s ) ) )' % (ATMV('q'), T1, ATMV('d'), T1))
val = w.s([dn, w.s([w.s([], 'ovex', '( %s x. ( d ^c %s ) ) e. _V' % (ATMV('d'), T1))], 'a1i',
                   '( %s -> ( %s x. ( d ^c %s ) ) e. _V )' % (AD, ATMV('d'), T1)),
           w.s([sub, w.s([], 'eqid', '%s = %s' % (AA, AA))], 'fvmptg',
               '( ( d e. NN /\\ ( %s x. ( d ^c %s ) ) e. _V ) -> ( %s ` d ) = ( %s x. ( d ^c %s ) ) )' % (ATMV('d'), T1, AA, ATMV('d'), T1))],
          'syl2anc', '( %s -> ( %s ` d ) = ( %s x. ( d ^c %s ) ) )' % (AD, AA, ATMV('d'), T1))
# the bound at d
sd = w.s([w.s([], 'breq1d', 'x') ], 'id', 'x')
w.lines.pop(); w.lines.pop()
sdsub = w.s([w.s([w.s([], 'fveq2', '( m = d -> ( S ` m ) = ( S ` d ) )')], 'fveq2d',
                 '( m = d -> ( abs ` ( S ` m ) ) = ( abs ` ( S ` d ) ) )')], 'breq1d',
            '( m = d -> ( ( abs ` ( S ` m ) ) <_ B <-> ( abs ` ( S ` d ) ) <_ B ) )')
sbd = w.s([sdsub, w.s([sall], 'adantr', '( %s -> A. m e. NN ( abs ` ( S ` m ) ) <_ B )' % AD), dn], 'rspcdva',
          '( %s -> ( abs ` ( S ` d ) ) <_ B )' % AD)
tm = w.s([w.s([w.s([scl, w.s([br], 'adantr', '( %s -> B e. RR )' % AD), sbd], '3jca',
                   '( %s -> ( ( S ` d ) e. CC /\\ B e. RR /\\ ( abs ` ( S ` d ) ) <_ B ) )' % AD),
               w.s([dn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % AD), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (AD, RZ))],
                   '3jca', '( %s -> ( d e. NN /\\ Z e. CC /\\ 0 < %s ) )' % (AD, RZ))], 'jca',
              '( %s -> ( ( ( S ` d ) e. CC /\\ B e. RR /\\ ( abs ` ( S ` d ) ) <_ B ) /\\ ( d e. NN /\\ Z e. CC /\\ 0 < %s ) ) )' % (AD, RZ)),
          w.inst('abtmbnd')], 'syl',
         '( %s -> ( abs ` %s ) <_ ( %s x. ( d ^c -u %s ) ) )' % (AD, ATMV('d'), BZ, T1))
# multiply by ( d ^c T1 ) and cancel
absv = w.s([val], 'fveq2d', '( %s -> ( abs ` ( %s ` d ) ) = ( abs ` ( %s x. ( d ^c %s ) ) ) )' % (AD, AA, ATMV('d'), T1))
amul = w.s([atc, w.s([dt1], 'rpcnd', '( %s -> ( d ^c %s ) e. CC )' % (AD, T1))], 'absmuld',
           '( %s -> ( abs ` ( %s x. ( d ^c %s ) ) ) = ( ( abs ` %s ) x. ( abs ` ( d ^c %s ) ) ) )' % (AD, ATMV('d'), T1, ATMV('d'), T1))
adt = w.s([w.s([dt1], 'rpred', '( %s -> ( d ^c %s ) e. RR )' % (AD, T1)),
           w.s([dt1], 'rpge0d', '( %s -> 0 <_ ( d ^c %s ) )' % (AD, T1))], 'absidd',
          '( %s -> ( abs ` ( d ^c %s ) ) = ( d ^c %s ) )' % (AD, T1, T1))
dmt1 = w.s([drp, w.s([t1d], 'renegcld', '( %s -> -u %s e. RR )' % (AD, T1))], 'rpcxpcld',
           '( %s -> ( d ^c -u %s ) e. RR+ )' % (AD, T1))
bzd = w.s([w.s([br], 'adantr', '( %s -> B e. RR )' % AD),
           w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % AD)], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % AD)],
          'remulcld', '( %s -> %s e. RR )' % (AD, BZ))
prod = w.s([w.s([atc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (AD, ATMV('d'))),
            w.s([bzd, w.s([dmt1], 'rpred', '( %s -> ( d ^c -u %s ) e. RR )' % (AD, T1))], 'remulcld',
                '( %s -> ( %s x. ( d ^c -u %s ) ) e. RR )' % (AD, BZ, T1)),
            w.s([dt1], 'rpred', '( %s -> ( d ^c %s ) e. RR )' % (AD, T1)),
            w.s([dt1], 'rpge0d', '( %s -> 0 <_ ( d ^c %s ) )' % (AD, T1)), tm], 'lemul1ad',
           '( %s -> ( ( abs ` %s ) x. ( d ^c %s ) ) <_ ( ( %s x. ( d ^c -u %s ) ) x. ( d ^c %s ) ) )' % (AD, ATMV('d'), T1, BZ, T1, T1))
# ( ( BZ x. ( d ^c -u T1 ) ) x. ( d ^c T1 ) ) = BZ
t1c = w.s([t1d], 'recnd', '( %s -> %s e. CC )' % (AD, T1))
nt1c = w.s([t1c], 'negcld', '( %s -> -u %s e. CC )' % (AD, T1))
cadd = w.s([w.s([dc, w.s([drp], 'rpne0d', '( %s -> d =/= 0 )' % AD)], 'jca',
                '( %s -> ( d e. CC /\\ d =/= 0 ) )' % AD), nt1c, t1c, w.inst('cxpadd')], 'syl3anc',
           '( %s -> ( d ^c ( -u %s + %s ) ) = ( ( d ^c -u %s ) x. ( d ^c %s ) ) )' % (AD, T1, T1, T1, T1))
z0e = w.s([w.s([nt1c, t1c], 'addcomd', '( %s -> ( -u %s + %s ) = ( %s + -u %s ) )' % (AD, T1, T1, T1, T1)),
           w.s([t1c], 'negidd', '( %s -> ( %s + -u %s ) = 0 )' % (AD, T1, T1))], 'eqtrd',
          '( %s -> ( -u %s + %s ) = 0 )' % (AD, T1, T1))
cone = w.s([w.s([w.s([z0e], 'oveq2d', '( %s -> ( d ^c ( -u %s + %s ) ) = ( d ^c 0 ) )' % (AD, T1, T1)),
                 w.s([dc, w.inst('cxp0')], 'syl', '( %s -> ( d ^c 0 ) = 1 )' % AD)], 'eqtrd',
                '( %s -> ( d ^c ( -u %s + %s ) ) = 1 )' % (AD, T1, T1))], 'id',
           '( %s -> ( d ^c ( -u %s + %s ) ) = 1 )' % (AD, T1, T1))
w.lines.pop()
cone = w.s([w.s([z0e], 'oveq2d', '( %s -> ( d ^c ( -u %s + %s ) ) = ( d ^c 0 ) )' % (AD, T1, T1)),
            w.s([dc, w.inst('cxp0')], 'syl', '( %s -> ( d ^c 0 ) = 1 )' % AD)], 'eqtrd',
           '( %s -> ( d ^c ( -u %s + %s ) ) = 1 )' % (AD, T1, T1))
prodone = w.s([w.s([cadd], 'eqcomd',
                   '( %s -> ( ( d ^c -u %s ) x. ( d ^c %s ) ) = ( d ^c ( -u %s + %s ) ) )' % (AD, T1, T1, T1, T1)),
               cone], 'eqtrd', '( %s -> ( ( d ^c -u %s ) x. ( d ^c %s ) ) = 1 )' % (AD, T1, T1))
bzc = w.s([bzd], 'recnd', '( %s -> %s e. CC )' % (AD, BZ))
assoc = w.s([bzc, w.s([dmt1], 'rpcnd', '( %s -> ( d ^c -u %s ) e. CC )' % (AD, T1)),
             w.s([dt1], 'rpcnd', '( %s -> ( d ^c %s ) e. CC )' % (AD, T1))], 'mulassd',
            '( %s -> ( ( %s x. ( d ^c -u %s ) ) x. ( d ^c %s ) ) = ( %s x. ( ( d ^c -u %s ) x. ( d ^c %s ) ) ) )' % (AD, BZ, T1, T1, BZ, T1, T1))
cancel = w.s([assoc, w.s([w.s([prodone], 'oveq2d',
                              '( %s -> ( %s x. ( ( d ^c -u %s ) x. ( d ^c %s ) ) ) = ( %s x. 1 ) )' % (AD, BZ, T1, T1, BZ)),
                          w.s([bzc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AD, BZ, BZ))], 'eqtrd',
                         '( %s -> ( %s x. ( ( d ^c -u %s ) x. ( d ^c %s ) ) ) = %s )' % (AD, BZ, T1, T1, BZ))],
             'eqtrd', '( %s -> ( ( %s x. ( d ^c -u %s ) ) x. ( d ^c %s ) ) = %s )' % (AD, BZ, T1, T1, BZ))
# the bound at d
abd = w.s([w.s([absv, amul], 'eqtrd',
               '( %s -> ( abs ` ( %s ` d ) ) = ( ( abs ` %s ) x. ( abs ` ( d ^c %s ) ) ) )' % (AD, AA, ATMV('d'), T1)),
           w.s([adt], 'oveq2d',
               '( %s -> ( ( abs ` %s ) x. ( abs ` ( d ^c %s ) ) ) = ( ( abs ` %s ) x. ( d ^c %s ) ) )' % (AD, ATMV('d'), T1, ATMV('d'), T1))],
          'eqtrd', '( %s -> ( abs ` ( %s ` d ) ) = ( ( abs ` %s ) x. ( d ^c %s ) ) )' % (AD, AA, ATMV('d'), T1))
bnd = w.s([abd, w.s([prod, cancel], 'breqtrd',
                    '( %s -> ( ( abs ` %s ) x. ( d ^c %s ) ) <_ %s )' % (AD, ATMV('d'), T1, BZ))], 'eqbrtrd',
          '( %s -> ( abs ` ( %s ` d ) ) <_ %s )' % (AD, AA, BZ))
alld = w.s([bnd], 'ralrimiva', '( %s -> A. d e. NN ( abs ` ( %s ` d ) ) <_ %s )' % (A1, AA, BZ))
cbv = w.s([w.s([w.s([w.s([], 'fveq2', '( d = m -> ( %s ` d ) = ( %s ` m ) )' % (AA, AA))], 'fveq2d',
                    '( d = m -> ( abs ` ( %s ` d ) ) = ( abs ` ( %s ` m ) ) )' % (AA, AA))], 'breq1d',
                '( d = m -> ( ( abs ` ( %s ` d ) ) <_ %s <-> ( abs ` ( %s ` m ) ) <_ %s ) )' % (AA, BZ, AA, BZ))],
          'cbvralvw', '( A. d e. NN ( abs ` ( %s ` d ) ) <_ %s <-> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (AA, BZ, AA, BZ))
allm = w.s([alld, w.s([cbv], 'a1i',
                      '( %s -> ( A. d e. NN ( abs ` ( %s ` d ) ) <_ %s <-> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) )' % (A1, AA, BZ, AA, BZ))],
           'mpbid', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (A1, AA, BZ))
w.qed([fn, bzr, allm], '3jca',
      '( %s -> ( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) )' % (A1, AA, BZ, AA, BZ))
run4(w)
