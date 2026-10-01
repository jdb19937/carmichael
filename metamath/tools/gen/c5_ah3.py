"""C5, Abel holomorphy 3: the uniform majorants of the Abel terms and their
derivatives on an open box, the UH package for the Abel term functions on the
box, and the holomorphy of the Abel series there."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

RZ = '( Re ` Z )'
B_ = BX()
EL = '( L / 2 )'
CD = '( B x. ( 1 + ( ( 2 x. R ) x. ( ( 2 ^c %s ) / %s ) ) ) )' % (EL, EL)
BXH = '( ( L e. RR+ /\\ R e. RR ) /\\ Z e. %s )' % B_
INB = lambda Z: '( %s e. CC /\\ ( L < ( Re ` %s ) /\\ ( Re ` %s ) < R ) /\\ ( -u R < ( Im ` %s ) /\\ ( Im ` %s ) < R ) )' % (Z, Z, Z, Z, Z)


def absctx(w, A1, abs_):
    d = {}
    d['sf'] = w.s([abs_, w.inst('simp1')], 'syl', '( %s -> S : NN --> CC )' % A1)
    d['br'] = w.s([abs_, w.inst('simp2')], 'syl', '( %s -> B e. RR )' % A1)
    d['bq'] = w.s([abs_, w.inst('simp3')], 'syl', '( %s -> A. m e. NN ( abs ` ( S ` m ) ) <_ B )' % A1)
    return d


def sbnd(w, ante, K, bq, mk):
    """( ante -> ( abs ` ( S ` K ) ) <_ B )"""
    sb = w.s([w.s([w.s([], 'fveq2', '( m = %s -> ( S ` m ) = ( S ` %s ) )' % (K, K))], 'fveq2d', '( m = %s -> ( abs ` ( S ` m ) ) = ( abs ` ( S ` %s ) ) )' % (K, K))], 'breq1d',
             '( m = %s -> ( ( abs ` ( S ` m ) ) <_ B <-> ( abs ` ( S ` %s ) ) <_ B ) )' % (K, K))
    return w.s([sb, bq, mk], 'rspcdva', '( %s -> ( abs ` ( S ` %s ) ) <_ B )' % (ante, K))


def bxctx(w, A1, lrp, rr, zb):
    """steps from Z e. BX under A1: (Z e. CC, Re Z e. RR, L < Re Z, 0 < Re Z, |Z| <_ 2R, L e. RR, 0 < L)"""
    d = {}
    inb = w.s([zb, w.inst('elbxi')], 'syl', '( %s -> %s )' % (A1, INB('Z')))
    d['zc'] = zc = w.s([inb, w.inst('simp1')], 'syl', '( %s -> Z e. CC )' % A1)
    d['rz'] = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A1, RZ))
    d['lr'] = lr = w.s([lrp], 'rpred', '( %s -> L e. RR )' % A1)
    d['l0'] = l0 = w.s([lrp], 'rpgt0d', '( %s -> 0 < L )' % A1)
    d['lltz'] = lltz = w.s([w.s([inb, w.inst('simp2')], 'syl', '( %s -> ( L < %s /\\ %s < R ) )' % (A1, RZ, RZ))], 'simpld', '( %s -> L < %s )' % (A1, RZ))
    d['z0'] = w.s([a1(w, A1, '0re', '0 e. RR'), lr, d['rz'], l0, lltz], 'lttrd', '( %s -> 0 < %s )' % (A1, RZ))
    d['az'] = w.s([w.s([w.s([lr, w.s([lrp], 'rpge0d', '( %s -> 0 <_ L )' % A1), rr], '3jca', '( %s -> ( L e. RR /\\ 0 <_ L /\\ R e. RR ) )' % A1), zb], 'jca',
                      '( %s -> ( ( L e. RR /\\ 0 <_ L /\\ R e. RR ) /\\ Z e. %s ) )' % (A1, B_)), w.inst('bxabs')], 'syl', '( %s -> ( abs ` Z ) <_ ( 2 x. R ) )' % A1)
    return d


def cxpmono(w, ante, K, T1, T2, kn, t1r, t2r, le):
    """( ante -> ( K ^c -u T1 ) <_ ( K ^c -u T2 ) ) from le: T2 <_ T1"""
    kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % ante)
    nle = w.s([le, w.s([t2r, t1r], 'lenegd', '( %s -> ( %s <_ %s <-> -u %s <_ -u %s ) )' % (ante, T2, T1, T1, T2))], 'mpbid', '( %s -> -u %s <_ -u %s )' % (ante, T1, T2))
    return w.s([w.s([w.s([kr, w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % ante)], 'jca', '( %s -> ( K e. RR /\\ 1 <_ K ) )' % ante),
                     w.s([w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (ante, T1)), w.s([t2r], 'renegcld', '( %s -> -u %s e. RR )' % (ante, T2))], 'jca',
                         '( %s -> ( -u %s e. RR /\\ -u %s e. RR ) )' % (ante, T1, T2)), nle], '3jca',
                    '( %s -> ( ( K e. RR /\\ 1 <_ K ) /\\ ( -u %s e. RR /\\ -u %s e. RR ) /\\ -u %s <_ -u %s ) )' % (ante, T1, T2, T1, T2)), w.inst('cxplea')], 'syl',
               '( %s -> ( K ^c -u %s ) <_ ( K ^c -u %s ) )' % (ante, T1, T2))


# ---------------------------------------------------------------- abtbnd
w = W('abtbnd', 'The uniform bound on an Abel term on an open box in the right half-plane ( ~ abtmbnd , ~ bxabs ).')
A0 = '( ( %s /\\ K e. NN ) /\\ %s )' % (ABS, BXH)
abs_ = w.s([], 'simpll', '( %s -> %s )' % (A0, ABS))
d = absctx(w, A0, abs_)
kn = w.s([], 'simplr', '( %s -> K e. NN )' % A0)
lrp = w.s([], 'simprll', '( %s -> L e. RR+ )' % A0)
rr = w.s([], 'simprlr', '( %s -> R e. RR )' % A0)
zb = w.s([], 'simprr', '( %s -> Z e. %s )' % (A0, B_))
b = bxctx(w, A0, lrp, rr, zb)
sk = w.s([d['sf'], kn], 'ffvelcdmd', '( %s -> ( S ` K ) e. CC )' % A0)
sle = sbnd(w, A0, 'K', d['bq'], kn)
T1 = '( %s + 1 )' % RZ
bd = w.s([w.s([w.s([sk, d['br'], sle], '3jca', '( %s -> ( ( S ` K ) e. CC /\\ B e. RR /\\ ( abs ` ( S ` K ) ) <_ B ) )' % A0),
                w.s([kn, b['zc'], b['z0']], '3jca', '( %s -> ( K e. NN /\\ Z e. CC /\\ 0 < %s ) )' % (A0, RZ))], 'jca',
               '( %s -> ( ( ( S ` K ) e. CC /\\ B e. RR /\\ ( abs ` ( S ` K ) ) <_ B ) /\\ ( K e. NN /\\ Z e. CC /\\ 0 < %s ) ) )' % (A0, RZ)), w.inst('abtmbnd')], 'syl',
         '( %s -> ( abs ` %s ) <_ ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) )' % (A0, ATM('S', 'K', 'Z'), T1))
r1 = a1(w, A0, '1re', '1 e. RR')
t1r = w.s([b['rz'], r1], 'readdcld', '( %s -> %s e. RR )' % (A0, T1))
l1r = w.s([b['lr'], r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % A0)
le = w.s([b['lr'], b['rz'], r1, w.s([b['lr'], b['rz'], b['lltz']], 'ltled', '( %s -> L <_ %s )' % (A0, RZ))], 'leadd1dd', '( %s -> ( L + 1 ) <_ %s )' % (A0, T1))
mono = cxpmono(w, A0, 'K', T1, '( L + 1 )', kn, t1r, l1r, le)
az = w.s([b['zc']], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
b0 = w.s([a1(w, A0, '0re', '0 e. RR'), w.s([sk], 'abscld', '( %s -> ( abs ` ( S ` K ) ) e. RR )' % A0), d['br'], w.s([sk], 'absge0d', '( %s -> 0 <_ ( abs ` ( S ` K ) ) )' % A0), sle], 'letrd',
         '( %s -> 0 <_ B )' % A0)
r2r = w.s([a1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( %s -> ( 2 x. R ) e. RR )' % A0)
m1 = w.s([w.s([az, r2r, w.s([d['br'], b0], 'jca', '( %s -> ( B e. RR /\\ 0 <_ B ) )' % A0)], '3jca', '( %s -> ( ( abs ` Z ) e. RR /\\ ( 2 x. R ) e. RR /\\ ( B e. RR /\\ 0 <_ B ) ) )' % A0),
           b['az'], w.inst('lemul2a')], 'syl2anc', '( %s -> ( B x. ( abs ` Z ) ) <_ ( B x. ( 2 x. R ) ) )' % A0)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
p1 = w.s([krp, w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (A0, T1))], 'rpcxpcld', '( %s -> ( K ^c -u %s ) e. RR+ )' % (A0, T1))
p2 = w.s([krp, w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'rpcxpcld', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR+ )' % A0)
bz = w.s([d['br'], az], 'remulcld', '( %s -> ( B x. ( abs ` Z ) ) e. RR )' % A0)
b2r = w.s([d['br'], r2r], 'remulcld', '( %s -> ( B x. ( 2 x. R ) ) e. RR )' % A0)
m2 = w.s([bz, b2r, w.s([p1], 'rpred', '( %s -> ( K ^c -u %s ) e. RR )' % (A0, T1)), w.s([p2], 'rpred', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR )' % A0),
          w.s([d['br'], az, b0, w.s([b['zc']], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % A0)], 'mulge0d', '( %s -> 0 <_ ( B x. ( abs ` Z ) ) )' % A0),
          w.s([p1], 'rpge0d', '( %s -> 0 <_ ( K ^c -u %s ) )' % (A0, T1)), m1, mono], 'lemul12ad',
         '( %s -> ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) <_ ( ( B x. ( 2 x. R ) ) x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, T1))
k1c = w.s([w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)], 'nncnd', '( %s -> ( K + 1 ) e. CC )' % A0)
nz = w.s([b['zc']], 'negcld', '( %s -> -u Z e. CC )' % A0)
atc = w.s([sk, w.s([w.s([w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0), nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u Z ) e. CC )' % A0),
                    w.s([k1c, nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( ( K + 1 ) ^c -u Z ) e. CC )' % A0)], 'subcld',
                   '( %s -> ( ( K ^c -u Z ) - ( ( K + 1 ) ^c -u Z ) ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, ATM('S', 'K', 'Z')))
w.qed([w.s([atc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, ATM('S', 'K', 'Z'))), w.s([bz, w.s([p1], 'rpred', '( %s -> ( K ^c -u %s ) e. RR )' % (A0, T1))], 'remulcld',
                                                                                             '( %s -> ( ( B x. ( abs ` Z ) ) x. ( K ^c -u %s ) ) e. RR )' % (A0, T1)),
       w.s([b2r, w.s([p2], 'rpred', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR )' % A0)], 'remulcld', '( %s -> ( ( B x. ( 2 x. R ) ) x. ( K ^c -u ( L + 1 ) ) ) e. RR )' % A0), bd, m2],
      'letrd', '( %s -> ( abs ` %s ) <_ ( ( B x. ( 2 x. R ) ) x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, ATM('S', 'K', 'Z')))
run5(w)

# ---------------------------------------------------------------- abtdvb
w = W('abtdvb', 'The uniform bound on the derivative of an Abel term on an open box in the right half-plane '
      '( ~ lgcxpmvt , ~ logp1bnd , ~ bxabs ).')
A0 = '( ( %s /\\ K e. NN ) /\\ %s )' % (ABS, BXH)
abs_ = w.s([], 'simpll', '( %s -> %s )' % (A0, ABS))
d = absctx(w, A0, abs_)
kn = w.s([], 'simplr', '( %s -> K e. NN )' % A0)
lrp = w.s([], 'simprll', '( %s -> L e. RR+ )' % A0)
rr = w.s([], 'simprlr', '( %s -> R e. RR )' % A0)
zb = w.s([], 'simprr', '( %s -> Z e. %s )' % (A0, B_))
b = bxctx(w, A0, lrp, rr, zb)
sk = w.s([d['sf'], kn], 'ffvelcdmd', '( %s -> ( S ` K ) e. CC )' % A0)
sle = sbnd(w, A0, 'K', d['bq'], kn)
LK = '( ( log ` K ) x. ( K ^c -u Z ) )'; LK1 = '( ( log ` ( K + 1 ) ) x. ( ( K + 1 ) ^c -u Z ) )'
KP = '( K ^c ( -u %s - 1 ) )' % RZ
LG1 = '( log ` ( K + 1 ) )'
MB = '( ( 1 + ( ( abs ` Z ) x. %s ) ) x. %s )' % (LG1, KP)
mvt = w.s([w.s([w.s([kn, b['zc']], 'jca', '( %s -> ( K e. NN /\\ Z e. CC ) )' % A0), b['z0']], 'jca', '( %s -> ( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s ) )' % (A0, RZ)), w.inst('lgcxpmvt')], 'syl',
          '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A0, LK, LK1, MB))
k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
nz = w.s([b['zc']], 'negcld', '( %s -> -u Z e. CC )' % A0)
lkc = w.s([w.s([w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)], 'recnd', '( %s -> ( log ` K ) e. CC )' % A0),
           w.s([w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0), nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u Z ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, LK))
lg1r = w.s([w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'relogcld', '( %s -> %s e. RR )' % (A0, LG1))
lk1c = w.s([w.s([lg1r], 'recnd', '( %s -> %s e. CC )' % (A0, LG1)), w.s([w.s([k1n], 'nncnd', '( %s -> ( K + 1 ) e. CC )' % A0), nz, w.inst('cxpcl')], 'syl2anc',
                                                                     '( %s -> ( ( K + 1 ) ^c -u Z ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, LK1))
sw = w.s([w.s([lk1c, lkc], 'abssubd', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A0, LK1, LK, LK, LK1)), mvt], 'eqbrtrd',
         '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (A0, LK1, LK, MB))
DIFF = '( %s - %s )' % (LK1, LK)
dc = w.s([lk1c, lkc], 'subcld', '( %s -> %s e. CC )' % (A0, DIFF))
# the bound MB <_ ( 1 + c K^E ) K^(-sigma-1) <_ ( 1 + c ) K^E K^(-(L+1)) = ( 1 + c ) K^-(1+E)
elrp = w.s([lrp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, EL))
elr = w.s([elrp], 'rpred', '( %s -> %s e. RR )' % (A0, EL))
lgb = w.s([kn, elrp, w.inst('logp1bnd')], 'syl2anc', '( %s -> %s <_ ( ( ( 2 ^c %s ) / %s ) x. ( K ^c %s ) ) )' % (A0, LG1, EL, EL, EL))
Q = '( ( 2 ^c %s ) / %s )' % (EL, EL)
qrp = w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), elr], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (A0, EL)), elrp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, Q))
kerp = w.s([w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0), elr], 'rpcxpcld', '( %s -> ( K ^c %s ) e. RR+ )' % (A0, EL))
qk = w.s([qrp, kerp], 'rpmulcld', '( %s -> ( %s x. ( K ^c %s ) ) e. RR+ )' % (A0, Q, EL))
az = w.s([b['zc']], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
az0 = w.s([b['zc']], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % A0)
r2r = w.s([a1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( %s -> ( 2 x. R ) e. RR )' % A0)
k1r = w.s([k1n], 'nnred', '( %s -> ( K + 1 ) e. RR )' % A0)
lg10 = w.s([k1r, w.s([k1n], 'nnge1d', '( %s -> 1 <_ ( K + 1 ) )' % A0), w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (A0, LG1))
zl = w.s([az, r2r, lg1r, w.s([qk], 'rpred', '( %s -> ( %s x. ( K ^c %s ) ) e. RR )' % (A0, Q, EL)), az0, lg10, b['az'], lgb], 'lemul12ad',
         '( %s -> ( ( abs ` Z ) x. %s ) <_ ( ( 2 x. R ) x. ( %s x. ( K ^c %s ) ) ) )' % (A0, LG1, Q, EL))
r1 = a1(w, A0, '1re', '1 e. RR')
# ( 2 R ) ( Q K^E ) = ( ( 2 R ) Q ) K^E, and 1 <_ K^E so 1 + c K^E <_ ( 1 + c ) K^E
C1 = '( ( 2 x. R ) x. %s )' % Q
alg1 = w.s([w.s([r2r], 'recnd', '( %s -> ( 2 x. R ) e. CC )' % A0), w.s([qrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, Q)), w.s([kerp], 'rpcnd', '( %s -> ( K ^c %s ) e. CC )' % (A0, EL))],
           'mulassd', '( %s -> ( %s x. ( K ^c %s ) ) = ( ( 2 x. R ) x. ( %s x. ( K ^c %s ) ) ) )' % (A0, C1, EL, Q, EL))
zl2 = w.s([zl, w.s([alg1], 'eqcomd', '( %s -> ( ( 2 x. R ) x. ( %s x. ( K ^c %s ) ) ) = ( %s x. ( K ^c %s ) ) )' % (A0, Q, EL, C1, EL))], 'breqtrd',
          '( %s -> ( ( abs ` Z ) x. %s ) <_ ( %s x. ( K ^c %s ) ) )' % (A0, LG1, C1, EL))
ke1 = w.s([w.s([w.s([w.s([kn], 'nnred', '( %s -> K e. RR )' % A0), w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)], 'jca', '( %s -> ( K e. RR /\\ 1 <_ K ) )' % A0),
                w.s([a1(w, A0, '0re', '0 e. RR'), elr], 'jca', '( %s -> ( 0 e. RR /\\ %s e. RR ) )' % (A0, EL)), w.s([elrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, EL))], '3jca',
               '( %s -> ( ( K e. RR /\\ 1 <_ K ) /\\ ( 0 e. RR /\\ %s e. RR ) /\\ 0 <_ %s ) )' % (A0, EL, EL)), w.inst('cxplea')], 'syl', '( %s -> ( K ^c 0 ) <_ ( K ^c %s ) )' % (A0, EL))
ke1b = w.s([w.s([w.s([w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0), w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A0)], 'eqcomd', '( %s -> 1 = ( K ^c 0 ) )' % A0), ke1], 'eqbrtrd',
           '( %s -> 1 <_ ( K ^c %s ) )' % (A0, EL))
c1r = w.s([r2r, w.s([qrp], 'rpred', '( %s -> %s e. RR )' % (A0, Q))], 'remulcld', '( %s -> %s e. RR )' % (A0, C1))
c1ke = w.s([c1r, w.s([kerp], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EL))], 'remulcld', '( %s -> ( %s x. ( K ^c %s ) ) e. RR )' % (A0, C1, EL))
s1 = w.s([r1, w.s([az, lg1r], 'remulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. RR )' % (A0, LG1)), w.s([kerp], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EL)), c1ke, ke1b, zl2], 'le2addd',
         '( %s -> ( 1 + ( ( abs ` Z ) x. %s ) ) <_ ( ( K ^c %s ) + ( %s x. ( K ^c %s ) ) ) )' % (A0, LG1, EL, C1, EL))
dist = w.s([w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), w.s([c1r], 'recnd', '( %s -> %s e. CC )' % (A0, C1)), w.s([kerp], 'rpcnd', '( %s -> ( K ^c %s ) e. CC )' % (A0, EL))], 'adddird',
                '( %s -> ( ( 1 + %s ) x. ( K ^c %s ) ) = ( ( 1 x. ( K ^c %s ) ) + ( %s x. ( K ^c %s ) ) ) )' % (A0, C1, EL, EL, C1, EL)),
            w.s([w.s([w.s([kerp], 'rpcnd', '( %s -> ( K ^c %s ) e. CC )' % (A0, EL))], 'mullidd', '( %s -> ( 1 x. ( K ^c %s ) ) = ( K ^c %s ) )' % (A0, EL, EL))], 'oveq1d',
                '( %s -> ( ( 1 x. ( K ^c %s ) ) + ( %s x. ( K ^c %s ) ) ) = ( ( K ^c %s ) + ( %s x. ( K ^c %s ) ) ) )' % (A0, EL, C1, EL, EL, C1, EL))], 'eqtrd',
           '( %s -> ( ( 1 + %s ) x. ( K ^c %s ) ) = ( ( K ^c %s ) + ( %s x. ( K ^c %s ) ) ) )' % (A0, C1, EL, EL, C1, EL))
s1b = w.s([s1, w.s([dist], 'eqcomd', '( %s -> ( ( K ^c %s ) + ( %s x. ( K ^c %s ) ) ) = ( ( 1 + %s ) x. ( K ^c %s ) ) )' % (A0, EL, C1, EL, C1, EL))], 'breqtrd',
          '( %s -> ( 1 + ( ( abs ` Z ) x. %s ) ) <_ ( ( 1 + %s ) x. ( K ^c %s ) ) )' % (A0, LG1, C1, EL))
# KP <_ K^-(L+1)
T1 = '( %s + 1 )' % RZ
t1r = w.s([b['rz'], r1], 'readdcld', '( %s -> %s e. RR )' % (A0, T1))
l1r = w.s([b['lr'], r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % A0)
le = w.s([b['lr'], b['rz'], r1, w.s([b['lr'], b['rz'], b['lltz']], 'ltled', '( %s -> L <_ %s )' % (A0, RZ))], 'leadd1dd', '( %s -> ( L + 1 ) <_ %s )' % (A0, T1))
mono = cxpmono(w, A0, 'K', T1, '( L + 1 )', kn, t1r, l1r, le)
negd = w.s([w.s([w.s([b['rz']], 'recnd', '( %s -> %s e. CC )' % (A0, RZ)), a1(w, A0, 'ax-1cn', '1 e. CC')], 'negdid', '( %s -> -u %s = ( -u %s + -u 1 ) )' % (A0, T1, RZ)),
            w.s([w.s([w.s([b['rz']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))], 'recnd', '( %s -> -u %s e. CC )' % (A0, RZ)), a1(w, A0, 'ax-1cn', '1 e. CC')], 'negsubd',
                '( %s -> ( -u %s + -u 1 ) = ( -u %s - 1 ) )' % (A0, RZ, RZ))], 'eqtrd', '( %s -> -u %s = ( -u %s - 1 ) )' % (A0, T1, RZ))
mono2 = w.s([w.s([w.s([negd], 'oveq2d', '( %s -> ( K ^c -u %s ) = %s )' % (A0, T1, KP))], 'eqcomd', '( %s -> %s = ( K ^c -u %s ) )' % (A0, KP, T1)), mono], 'eqbrtrd',
            '( %s -> %s <_ ( K ^c -u ( L + 1 ) ) )' % (A0, KP))
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
kpr = w.s([w.s([krp, w.s([w.s([b['rz']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ)), r1], 'resubcld', '( %s -> ( -u %s - 1 ) e. RR )' % (A0, RZ))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, KP))],
          'rpred', '( %s -> %s e. RR )' % (A0, KP))
kp0 = w.s([w.s([krp, w.s([w.s([b['rz']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ)), r1], 'resubcld', '( %s -> ( -u %s - 1 ) e. RR )' % (A0, RZ))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, KP))],
          'rpge0d', '( %s -> 0 <_ %s )' % (A0, KP))
kl1 = w.s([krp, w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'rpcxpcld', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR+ )' % A0)
one_ = w.s([r1, w.s([az, lg1r], 'remulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. RR )' % (A0, LG1))], 'readdcld', '( %s -> ( 1 + ( ( abs ` Z ) x. %s ) ) e. RR )' % (A0, LG1))
one0 = w.s([r1, w.s([az, lg1r], 'remulcld', '( %s -> ( ( abs ` Z ) x. %s ) e. RR )' % (A0, LG1)), a1(w, A0, '0le1', '0 <_ 1'), w.s([az, lg1r, az0, lg10], 'mulge0d', '( %s -> 0 <_ ( ( abs ` Z ) x. %s ) )' % (A0, LG1))],
           'addge0d', '( %s -> 0 <_ ( 1 + ( ( abs ` Z ) x. %s ) ) )' % (A0, LG1))
c1ker = w.s([w.s([r1, c1r], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, C1)), w.s([kerp], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EL))], 'remulcld', '( %s -> ( ( 1 + %s ) x. ( K ^c %s ) ) e. RR )' % (A0, C1, EL))
m2 = w.s([one_, c1ker, kpr, w.s([kl1], 'rpred', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR )' % A0), one0, kp0, s1b, mono2], 'lemul12ad',
         '( %s -> %s <_ ( ( ( 1 + %s ) x. ( K ^c %s ) ) x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, MB, C1, EL))
# ( ( 1 + C1 ) K^E ) K^-(L+1) = ( 1 + C1 ) K^-(1+E)
kc = w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0)
elc = w.s([elr], 'recnd', '( %s -> %s e. CC )' % (A0, EL))
nl1c = w.s([w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'recnd', '( %s -> -u ( L + 1 ) e. CC )' % A0)
cadd = w.s([w.s([kc, w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)], 'jca', '( %s -> ( K e. CC /\\ K =/= 0 ) )' % A0), elc, nl1c, w.inst('cxpadd')], 'syl3anc',
           '( %s -> ( K ^c ( %s + -u ( L + 1 ) ) ) = ( ( K ^c %s ) x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, EL, EL))
lc = w.s([b['lr']], 'recnd', '( %s -> L e. CC )' % A0)
onec = a1(w, A0, 'ax-1cn', '1 e. CC')
# ( EL + -u ( L + 1 ) ) = -u ( 1 + EL )
e1 = w.s([elc, w.s([lc, onec], 'addcld', '( %s -> ( L + 1 ) e. CC )' % A0)], 'negsubd', '( %s -> ( %s + -u ( L + 1 ) ) = ( %s - ( L + 1 ) ) )' % (A0, EL, EL))
e2 = w.s([w.s([elc, lc, onec], 'subsub4d', '( %s -> ( ( %s - L ) - 1 ) = ( %s - ( L + 1 ) ) )' % (A0, EL, EL))], 'eqcomd', '( %s -> ( %s - ( L + 1 ) ) = ( ( %s - L ) - 1 ) )' % (A0, EL, EL))
hv = w.s([lc, w.inst('2halves')], 'syl', '( %s -> ( %s + %s ) = L )' % (A0, EL, EL))
e3 = w.s([w.s([w.s([hv], 'eqcomd', '( %s -> L = ( %s + %s ) )' % (A0, EL, EL))], 'oveq2d', '( %s -> ( %s - L ) = ( %s - ( %s + %s ) ) )' % (A0, EL, EL, EL, EL)),
          w.s([w.s([w.s([elc, elc, elc], 'subsub4d', '( %s -> ( ( %s - %s ) - %s ) = ( %s - ( %s + %s ) ) )' % (A0, EL, EL, EL, EL, EL, EL))], 'eqcomd',
                   '( %s -> ( %s - ( %s + %s ) ) = ( ( %s - %s ) - %s ) )' % (A0, EL, EL, EL, EL, EL, EL)),
               w.s([w.s([w.s([elc], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (A0, EL, EL))], 'oveq1d', '( %s -> ( ( %s - %s ) - %s ) = ( 0 - %s ) )' % (A0, EL, EL, EL, EL)),
                    w.s([w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (EL, EL))], 'eqcomi', '( 0 - %s ) = -u %s' % (EL, EL))], 'a1i', '( %s -> ( 0 - %s ) = -u %s )' % (A0, EL, EL))], 'eqtrd',
                   '( %s -> ( ( %s - %s ) - %s ) = -u %s )' % (A0, EL, EL, EL, EL))], 'eqtrd', '( %s -> ( %s - ( %s + %s ) ) = -u %s )' % (A0, EL, EL, EL, EL))], 'eqtrd',
         '( %s -> ( %s - L ) = -u %s )' % (A0, EL, EL))
e4 = w.s([w.s([e3], 'oveq1d', '( %s -> ( ( %s - L ) - 1 ) = ( -u %s - 1 ) )' % (A0, EL, EL)),
          w.s([w.s([w.s([w.s([elc], 'negcld', '( %s -> -u %s e. CC )' % (A0, EL)), onec], 'negsubd', '( %s -> ( -u %s + -u 1 ) = ( -u %s - 1 ) )' % (A0, EL, EL))], 'eqcomd',
                   '( %s -> ( -u %s - 1 ) = ( -u %s + -u 1 ) )' % (A0, EL, EL)),
               w.s([w.s([w.s([elc], 'negcld', '( %s -> -u %s e. CC )' % (A0, EL)), a1(w, A0, 'neg1cn', '-u 1 e. CC')], 'addcomd', '( %s -> ( -u %s + -u 1 ) = ( -u 1 + -u %s ) )' % (A0, EL, EL)),
                    w.s([w.s([onec, elc], 'negdid', '( %s -> -u ( 1 + %s ) = ( -u 1 + -u %s ) )' % (A0, EL, EL))], 'eqcomd', '( %s -> ( -u 1 + -u %s ) = -u ( 1 + %s ) )' % (A0, EL, EL))], 'eqtrd',
                   '( %s -> ( -u %s + -u 1 ) = -u ( 1 + %s ) )' % (A0, EL, EL))], 'eqtrd', '( %s -> ( -u %s - 1 ) = -u ( 1 + %s ) )' % (A0, EL, EL))], 'eqtrd',
         '( %s -> ( ( %s - L ) - 1 ) = -u ( 1 + %s ) )' % (A0, EL, EL))
expeq = w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( %s + -u ( L + 1 ) ) = ( ( %s - L ) - 1 ) )' % (A0, EL, EL)), e4], 'eqtrd', '( %s -> ( %s + -u ( L + 1 ) ) = -u ( 1 + %s ) )' % (A0, EL, EL))
prod = w.s([w.s([w.s([cadd], 'eqcomd', '( %s -> ( ( K ^c %s ) x. ( K ^c -u ( L + 1 ) ) ) = ( K ^c ( %s + -u ( L + 1 ) ) ) )' % (A0, EL, EL)),
                 w.s([expeq], 'oveq2d', '( %s -> ( K ^c ( %s + -u ( L + 1 ) ) ) = ( K ^c -u ( 1 + %s ) ) )' % (A0, EL, EL))], 'eqtrd',
                '( %s -> ( ( K ^c %s ) x. ( K ^c -u ( L + 1 ) ) ) = ( K ^c -u ( 1 + %s ) ) )' % (A0, EL, EL))], 'idi', '( %s -> ( ( K ^c %s ) x. ( K ^c -u ( L + 1 ) ) ) = ( K ^c -u ( 1 + %s ) ) )' % (A0, EL, EL))
c1c = w.s([r1, c1r], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, C1))
alg2 = w.s([w.s([w.s([c1c], 'recnd', '( %s -> ( 1 + %s ) e. CC )' % (A0, C1)), w.s([kerp], 'rpcnd', '( %s -> ( K ^c %s ) e. CC )' % (A0, EL)), w.s([kl1], 'rpcnd', '( %s -> ( K ^c -u ( L + 1 ) ) e. CC )' % A0)],
                'mulassd', '( %s -> ( ( ( 1 + %s ) x. ( K ^c %s ) ) x. ( K ^c -u ( L + 1 ) ) ) = ( ( 1 + %s ) x. ( ( K ^c %s ) x. ( K ^c -u ( L + 1 ) ) ) ) )' % (A0, C1, EL, C1, EL)),
            w.s([prod], 'oveq2d', '( %s -> ( ( 1 + %s ) x. ( ( K ^c %s ) x. ( K ^c -u ( L + 1 ) ) ) ) = ( ( 1 + %s ) x. ( K ^c -u ( 1 + %s ) ) ) )' % (A0, C1, EL, C1, EL))], 'eqtrd',
           '( %s -> ( ( ( 1 + %s ) x. ( K ^c %s ) ) x. ( K ^c -u ( L + 1 ) ) ) = ( ( 1 + %s ) x. ( K ^c -u ( 1 + %s ) ) ) )' % (A0, C1, EL, C1, EL))
m3 = w.s([m2, alg2], 'breqtrd', '( %s -> %s <_ ( ( 1 + %s ) x. ( K ^c -u ( 1 + %s ) ) ) )' % (A0, MB, C1, EL))
# |DAT| = |S_K| |DIFF| <_ B x. MB <_ B x. ( ( 1 + C1 ) K^-(1+E) ) = CD x. K^-(1+E)
mbr = w.s([one_, kpr], 'remulcld', '( %s -> %s e. RR )' % (A0, MB))
KE1 = '( K ^c -u ( 1 + %s ) )' % EL
ke1rp = w.s([krp, w.s([w.s([r1, elr], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, EL))], 'renegcld', '( %s -> -u ( 1 + %s ) e. RR )' % (A0, EL))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, KE1))
rhsr = w.s([c1c, w.s([ke1rp], 'rpred', '( %s -> %s e. RR )' % (A0, KE1))], 'remulcld', '( %s -> ( ( 1 + %s ) x. %s ) e. RR )' % (A0, C1, KE1))
b0 = w.s([a1(w, A0, '0re', '0 e. RR'), w.s([sk], 'abscld', '( %s -> ( abs ` ( S ` K ) ) e. RR )' % A0), d['br'], w.s([sk], 'absge0d', '( %s -> 0 <_ ( abs ` ( S ` K ) ) )' % A0), sle], 'letrd', '( %s -> 0 <_ B )' % A0)
m4 = w.s([w.s([sk], 'abscld', '( %s -> ( abs ` ( S ` K ) ) e. RR )' % A0), d['br'], w.s([dc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, DIFF)), rhsr,
          w.s([sk], 'absge0d', '( %s -> 0 <_ ( abs ` ( S ` K ) ) )' % A0), w.s([dc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, DIFF)), sle,
          w.s([w.s([dc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, DIFF)), mbr, rhsr, sw, m3], 'letrd', '( %s -> ( abs ` %s ) <_ ( ( 1 + %s ) x. %s ) )' % (A0, DIFF, C1, KE1))], 'lemul12ad',
         '( %s -> ( ( abs ` ( S ` K ) ) x. ( abs ` %s ) ) <_ ( B x. ( ( 1 + %s ) x. %s ) ) )' % (A0, DIFF, C1, KE1))
absd = w.s([sk, dc], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` ( S ` K ) ) x. ( abs ` %s ) ) )' % (A0, DAT('S', 'K', 'Z'), DIFF))
alg3 = w.s([w.s([w.s([d['br']], 'recnd', '( %s -> B e. CC )' % A0), w.s([c1c], 'recnd', '( %s -> ( 1 + %s ) e. CC )' % (A0, C1)), w.s([ke1rp], 'rpcnd', '( %s -> %s e. CC )' % (A0, KE1))], 'mulassd',
                '( %s -> ( ( B x. ( 1 + %s ) ) x. %s ) = ( B x. ( ( 1 + %s ) x. %s ) ) )' % (A0, C1, KE1, C1, KE1))], 'eqcomd',
           '( %s -> ( B x. ( ( 1 + %s ) x. %s ) ) = ( %s x. %s ) )' % (A0, C1, KE1, CD, KE1))
w.qed([w.s([absd, m4], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( B x. ( ( 1 + %s ) x. %s ) ) )' % (A0, DAT('S', 'K', 'Z'), C1, KE1)), alg3], 'breqtrd',
      '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, DAT('S', 'K', 'Z'), CD, KE1))
run5(w)
