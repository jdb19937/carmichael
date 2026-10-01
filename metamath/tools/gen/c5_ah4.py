"""C5, Abel holomorphy 4: the UH package of the Abel term functions on an open
box, the holomorphy of the Abel series on the box, on the half-plane (holloc),
and for a nonprincipal character."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

RZ = '( Re ` Z )'
B_ = BX()
EL = '( L / 2 )'
CD = '( B x. ( 1 + ( ( 2 x. R ) x. ( ( 2 ^c %s ) / %s ) ) ) )' % (EL, EL)
BXA = '( %s /\\ ( L e. RR+ /\\ R e. RR ) )' % ABS
MAJA = '( n e. NN |-> ( ( B x. ( 2 x. R ) ) x. ( n ^c -u ( L + 1 ) ) ) )'
MAJAD = '( n e. NN |-> ( %s x. ( n ^c -u ( 1 + %s ) ) ) )' % (CD, EL)
AB = ABF('S', B_)
INBP = lambda P: '( p e. %s |-> %s )' % (B_, ATM('S', P, 'p'))
bxex = lambda w, ante: w.s([w.s([w.s([], 'bxopn', '%s e. %s' % (B_, TOP))], 'elexi', '%s e. _V' % B_)], 'a1i', '( %s -> %s e. _V )' % (ante, B_))


def abfv(w, ante, K, mk):
    """( ante -> ( ABF ` K ) = ( p e. BX |-> ATM(S,K,p) ) )"""
    s1 = w.s([w.s([], 'fveq2', '( a = %s -> ( S ` a ) = ( S ` %s ) )' % (K, K)),
              w.s([w.s([], 'oveq1', '( a = %s -> ( a ^c -u p ) = ( %s ^c -u p ) )' % (K, K)),
                   w.s([w.s([], 'oveq1', '( a = %s -> ( a + 1 ) = ( %s + 1 ) )' % (K, K))], 'oveq1d', '( a = %s -> ( ( a + 1 ) ^c -u p ) = ( ( %s + 1 ) ^c -u p ) )' % (K, K))], 'oveq12d',
                  '( a = %s -> ( ( a ^c -u p ) - ( ( a + 1 ) ^c -u p ) ) = ( ( %s ^c -u p ) - ( ( %s + 1 ) ^c -u p ) ) )' % (K, K, K))], 'oveq12d',
             '( a = %s -> %s = %s )' % (K, ATM('S', 'a', 'p'), ATM('S', K, 'p')))
    s2 = w.s([s1], 'mpteq2dv', '( a = %s -> %s = %s )' % (K, INBP('a'), INBP(K)))
    ex = w.s([w.s([w.s([w.s([], 'bxopn', '%s e. %s' % (B_, TOP))], 'elexi', '%s e. _V' % B_)], 'mptex', '%s e. _V' % INBP(K))], 'a1i', '( %s -> %s e. _V )' % (ante, INBP(K)))
    fv = w.s([s2, w.s([], 'eqid', '%s = %s' % (AB, AB))], 'fvmptg', '( ( %s e. NN /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (K, INBP(K), AB, K, INBP(K)))
    return w.s([mk, ex, fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, AB, K, INBP(K)))


def atmval(w, ante, K, Z, mz):
    """( ante -> ( ( p e. BX |-> ATM(S,K,p) ) ` Z ) = ATM(S,K,Z) )"""
    sub = w.s([w.s([w.s([w.s([], 'negeq', '( p = %s -> -u p = -u %s )' % (Z, Z))], 'oveq2d', '( p = %s -> ( %s ^c -u p ) = ( %s ^c -u %s ) )' % (Z, K, K, Z)),
                    w.s([w.s([], 'negeq', '( p = %s -> -u p = -u %s )' % (Z, Z))], 'oveq2d', '( p = %s -> ( ( %s + 1 ) ^c -u p ) = ( ( %s + 1 ) ^c -u %s ) )' % (Z, K, K, Z))], 'oveq12d',
                   '( p = %s -> ( ( %s ^c -u p ) - ( ( %s + 1 ) ^c -u p ) ) = ( ( %s ^c -u %s ) - ( ( %s + 1 ) ^c -u %s ) ) )' % (Z, K, K, K, Z, K, Z))], 'oveq2d',
              '( p = %s -> %s = %s )' % (Z, ATM('S', K, 'p'), ATM('S', K, Z)))
    return mpv(w, ante, INBP(K), Z, ATM('S', K, Z), sub, mz, vexd(w, ante, ATM('S', K, Z)), B_)


def datval(w, ante, K, Z, mz):
    sub = w.s([w.s([w.s([w.s([], 'negeq', '( p = %s -> -u p = -u %s )' % (Z, Z))], 'oveq2d', '( p = %s -> ( ( %s + 1 ) ^c -u p ) = ( ( %s + 1 ) ^c -u %s ) )' % (Z, K, K, Z))], 'oveq2d',
                   '( p = %s -> ( ( log ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u p ) ) = ( ( log ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u %s ) ) )' % (Z, K, K, K, K, Z)),
               w.s([w.s([w.s([], 'negeq', '( p = %s -> -u p = -u %s )' % (Z, Z))], 'oveq2d', '( p = %s -> ( %s ^c -u p ) = ( %s ^c -u %s ) )' % (Z, K, K, Z))], 'oveq2d',
                   '( p = %s -> ( ( log ` %s ) x. ( %s ^c -u p ) ) = ( ( log ` %s ) x. ( %s ^c -u %s ) ) )' % (Z, K, K, K, K, Z))], 'oveq12d',
              '( p = %s -> ( ( ( log ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u p ) ) - ( ( log ` %s ) x. ( %s ^c -u p ) ) ) = ( ( ( log ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u %s ) ) - ( ( log ` %s ) x. ( %s ^c -u %s ) ) ) )' % (
                  Z, K, K, K, K, K, K, Z, K, K, Z))
    sub2 = w.s([sub], 'oveq2d', '( p = %s -> %s = %s )' % (Z, DAT('S', K, 'p'), DAT('S', K, Z)))
    MPD = '( p e. %s |-> %s )' % (B_, DAT('S', K, 'p'))
    return mpv(w, ante, MPD, Z, DAT('S', K, Z), sub2, mz, vexd(w, ante, DAT('S', K, Z)), B_)


# ---------------------------------------------------------------- abbxuh
w = W('abbxuh', 'The Abel term functions of a bounded partial-sum sequence on an open box in the right '
      'half-plane satisfy the hypotheses of the uniform-limit theorem ~ uhhol ( ~ abtbnd , ~ abtdvb ).')
A0 = BXA
abs_ = w.s([], 'simpl', '( %s -> %s )' % (A0, ABS))
sf = w.s([abs_, w.inst('simp1')], 'syl', '( %s -> S : NN --> CC )' % A0)
br = w.s([abs_, w.inst('simp2')], 'syl', '( %s -> B e. RR )' % A0)
lrp = w.s([], 'simprl', '( %s -> L e. RR+ )' % A0)
rr = w.s([], 'simprr', '( %s -> R e. RR )' % A0)
lr = w.s([lrp], 'rpred', '( %s -> L e. RR )' % A0)
bo = a1(w, A0, 'bxopn', '%s e. %s' % (B_, TOP))
# ABF : NN --> ( CC ^m BX )
Aa = '( %s /\\ a e. NN )' % A0
an = w.s([], 'simpr', '( %s -> a e. NN )' % Aa)
Aap = '( %s /\\ p e. %s )' % (Aa, B_)
pc = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (Aap, B_)), w.inst('elbxi')], 'syl', '( %s -> ( p e. CC /\\ ( L < ( Re ` p ) /\\ ( Re ` p ) < R ) /\\ ( -u R < ( Im ` p ) /\\ ( Im ` p ) < R ) ) )' % Aap),
          w.inst('simp1')], 'syl', '( %s -> p e. CC )' % Aap)
np = w.s([pc], 'negcld', '( %s -> -u p e. CC )' % Aap)
ann = w.s([an], 'adantr', '( %s -> a e. NN )' % Aap)
tc = w.s([w.s([w.s([sf], 'ad2antrr', '( %s -> S : NN --> CC )' % Aap), ann], 'ffvelcdmd', '( %s -> ( S ` a ) e. CC )' % Aap),
          w.s([w.s([w.s([ann], 'nncnd', '( %s -> a e. CC )' % Aap), np, w.inst('cxpcl')], 'syl2anc', '( %s -> ( a ^c -u p ) e. CC )' % Aap),
               w.s([w.s([w.s([ann, w.inst('peano2nn')], 'syl', '( %s -> ( a + 1 ) e. NN )' % Aap)], 'nncnd', '( %s -> ( a + 1 ) e. CC )' % Aap), np, w.inst('cxpcl')], 'syl2anc',
                   '( %s -> ( ( a + 1 ) ^c -u p ) e. CC )' % Aap)], 'subcld', '( %s -> ( ( a ^c -u p ) - ( ( a + 1 ) ^c -u p ) ) e. CC )' % Aap)], 'mulcld',
         '( %s -> %s e. CC )' % (Aap, ATM('S', 'a', 'p')))
mf = w.s([tc, w.s([], 'eqid', '%s = %s' % (INBP('a'), INBP('a')))], 'fmptd', '( %s -> %s : %s --> CC )' % (Aa, INBP('a'), B_))
mm = elmapf(w, Aa, INBP('a'), bxex(w, Aa), mf, B_)
fm = w.s([mm, w.s([], 'eqid', '%s = %s' % (AB, AB))], 'fmptd', '( %s -> %s : NN --> ( CC ^m %s ) )' % (A0, AB, B_))
# termwise HOL
Aj = '( %s /\\ j e. NN )' % A0
jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
sv = abfv(w, Aj, 'j', jn)
hol = w.s([w.s([w.s([w.s([sf], 'adantr', '( %s -> S : NN --> CC )' % Aj), jn], 'jca', '( %s -> ( S : NN --> CC /\\ j e. NN ) )' % Aj), w.s([bo], 'adantr', '( %s -> %s e. %s )' % (Aj, B_, TOP))],
               'jca', '( %s -> ( ( S : NN --> CC /\\ j e. NN ) /\\ %s e. %s ) )' % (Aj, B_, TOP)), w.inst('abthol')], 'syl', '( %s -> %s )' % (Aj, HOLG2(INBP('j'), B_)))
c1 = w.s([sv, w.s([hol], 'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Aj, INBP('j'), B_))], 'eqeltrd', '( %s -> ( %s ` j ) e. ( %s -cn-> CC ) )' % (Aj, AB, B_))
dm = w.s([w.s([sv], 'oveq2d', '( %s -> ( CC _D ( %s ` j ) ) = ( CC _D %s ) )' % (Aj, AB, INBP('j')))], 'dmeqd', '( %s -> dom ( CC _D ( %s ` j ) ) = dom ( CC _D %s ) )' % (Aj, AB, INBP('j')))
c2 = w.s([w.s([hol], 'simprd', '( %s -> %s C_ dom ( CC _D %s ) )' % (Aj, B_, INBP('j'))), dm], 'sseqtrrd', '( %s -> %s C_ dom ( CC _D ( %s ` j ) ) )' % (Aj, B_, AB))
UT = UHT(AB, B_)
ral = w.s([w.s([c1, c2], 'jca', '( %s -> %s )' % (Aj, HOLG2('( %s ` j )' % AB, B_)))], 'ralrimiva', '( %s -> %s )' % (A0, UT))
left = w.s([fm, ral], 'jca', '( %s -> ( %s : NN --> ( CC ^m %s ) /\\ %s ) )' % (A0, AB, B_, UT))
# the majorant M
r1 = a1(w, A0, '1re', '1 e. RR')
l1r = w.s([lr, r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % A0)
l1gt = w.s([w.s([w.s([r1, lrp, w.inst('ltaddrp')], 'syl2anc', '( %s -> 1 < ( 1 + L ) )' % A0), w.s([w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), w.s([lr], 'recnd', '( %s -> L e. CC )' % A0)], 'addcomd',
                                                                                                            '( %s -> ( 1 + L ) = ( L + 1 ) )' % A0)], 'idi', '( %s -> ( 1 + L ) = ( L + 1 ) )' % A0)],
              'breqtrd', '( %s -> 1 < ( L + 1 ) )' % A0)], 'idi', '( %s -> 1 < ( L + 1 ) )' % A0)
CB = '( B x. ( 2 x. R ) )'
cbr = w.s([br, w.s([a1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( %s -> ( 2 x. R ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, CB))
An = '( %s /\\ n e. NN )' % A0
nn = w.s([], 'simpr', '( %s -> n e. NN )' % An)
mre = w.s([w.s([cbr], 'adantr', '( %s -> %s e. RR )' % (An, CB)), w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An), w.s([w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'adantr',
                                                                                                                                '( %s -> -u ( L + 1 ) e. RR )' % An)], 'rpcxpcld',
                                                                        '( %s -> ( n ^c -u ( L + 1 ) ) e. RR+ )' % An)], 'rpred', '( %s -> ( n ^c -u ( L + 1 ) ) e. RR )' % An)], 'remulcld',
          '( %s -> ( %s x. ( n ^c -u ( L + 1 ) ) ) e. RR )' % (An, CB))
mf2 = w.s([mre, w.s([], 'eqid', '%s = %s' % (MAJA, MAJA))], 'fmptd', '( %s -> %s : NN --> RR )' % (A0, MAJA))
mcv = w.s([w.s([w.s([l1r, l1gt], 'jca', '( %s -> ( ( L + 1 ) e. RR /\\ 1 < ( L + 1 ) ) )' % A0), w.s([cbr], 'recnd', '( %s -> %s e. CC )' % (A0, CB))], 'jca',
               '( %s -> ( ( ( L + 1 ) e. RR /\\ 1 < ( L + 1 ) ) /\\ %s e. CC ) )' % (A0, CB)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAJA))
Ajy = '( %s /\\ ( j e. NN /\\ y e. %s ) )' % (A0, B_)
jn2 = w.s([], 'simprl', '( %s -> j e. NN )' % Ajy)
yb = w.s([], 'simprr', '( %s -> y e. %s )' % (Ajy, B_))
BXY = '( ( L e. RR+ /\\ R e. RR ) /\\ y e. %s )' % B_
pk = w.s([w.s([w.s([abs_], 'adantr', '( %s -> %s )' % (Ajy, ABS)), jn2], 'jca', '( %s -> ( %s /\\ j e. NN ) )' % (Ajy, ABS)),
          w.s([w.s([w.s([], 'simpr', '( %s -> ( L e. RR+ /\\ R e. RR ) )' % A0)], 'adantr', '( %s -> ( L e. RR+ /\\ R e. RR ) )' % Ajy), yb], 'jca', '( %s -> %s )' % (Ajy, BXY))], 'jca',
         '( %s -> ( ( %s /\\ j e. NN ) /\\ %s ) )' % (Ajy, ABS, BXY))
bd = w.s([pk, w.inst('abtbnd')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. ( j ^c -u ( L + 1 ) ) ) )' % (Ajy, ATM('S', 'j', 'y'), CB))
vv = w.s([w.s([abfv(w, Ajy, 'j', jn2)], 'fveq1d', '( %s -> ( ( %s ` j ) ` y ) = ( %s ` y ) )' % (Ajy, AB, INBP('j'))), atmval(w, Ajy, 'j', 'y', yb)], 'eqtrd',
         '( %s -> ( ( %s ` j ) ` y ) = %s )' % (Ajy, AB, ATM('S', 'j', 'y')))
subm = w.s([w.s([], 'oveq1', '( n = j -> ( n ^c -u ( L + 1 ) ) = ( j ^c -u ( L + 1 ) ) )')], 'oveq2d', '( n = j -> ( %s x. ( n ^c -u ( L + 1 ) ) ) = ( %s x. ( j ^c -u ( L + 1 ) ) ) )' % (CB, CB))
mv = mpv(w, Ajy, MAJA, 'j', '( %s x. ( j ^c -u ( L + 1 ) ) )' % CB, subm, jn2, vexd(w, Ajy, '( %s x. ( j ^c -u ( L + 1 ) ) )' % CB))
bd2 = w.s([w.s([w.s([vv], 'fveq2d', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s ) )' % (Ajy, AB, ATM('S', 'j', 'y'))), bd], 'eqbrtrd',
                '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s x. ( j ^c -u ( L + 1 ) ) ) )' % (Ajy, AB, CB)), mv], 'breqtrrd', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (Ajy, AB, MAJA))
mb = w.s([bd2], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (A0, B_, AB, MAJA))
um = w.s([mf2, mcv, mb], '3jca', '( %s -> %s )' % (A0, UHM(AB, MAJA, B_)))
# the majorant R
elrp = w.s([lrp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, EL))
elr = w.s([elrp], 'rpred', '( %s -> %s e. RR )' % (A0, EL))
e1r = w.s([r1, elr], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, EL))
e1gt = w.s([r1, elrp, w.inst('ltaddrp')], 'syl2anc', '( %s -> 1 < ( 1 + %s ) )' % (A0, EL))
Q = '( ( 2 ^c %s ) / %s )' % (EL, EL)
qr = w.s([w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), elr], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (A0, EL)), elrp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, Q))], 'rpred', '( %s -> %s e. RR )' % (A0, Q))
cdr = w.s([br, w.s([r1, w.s([w.s([a1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( %s -> ( 2 x. R ) e. RR )' % A0), qr], 'remulcld', '( %s -> ( ( 2 x. R ) x. %s ) e. RR )' % (A0, Q))], 'readdcld',
                  '( %s -> ( 1 + ( ( 2 x. R ) x. %s ) ) e. RR )' % (A0, Q))], 'remulcld', '( %s -> %s e. RR )' % (A0, CD))
rre = w.s([w.s([cdr], 'adantr', '( %s -> %s e. RR )' % (An, CD)), w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An), w.s([w.s([e1r], 'renegcld', '( %s -> -u ( 1 + %s ) e. RR )' % (A0, EL))], 'adantr',
                                                                                                                                '( %s -> -u ( 1 + %s ) e. RR )' % (An, EL))], 'rpcxpcld',
                                                                        '( %s -> ( n ^c -u ( 1 + %s ) ) e. RR+ )' % (An, EL))], 'rpred', '( %s -> ( n ^c -u ( 1 + %s ) ) e. RR )' % (An, EL))], 'remulcld',
          '( %s -> ( %s x. ( n ^c -u ( 1 + %s ) ) ) e. RR )' % (An, CD, EL))
rf = w.s([rre, w.s([], 'eqid', '%s = %s' % (MAJAD, MAJAD))], 'fmptd', '( %s -> %s : NN --> RR )' % (A0, MAJAD))
rcv = w.s([w.s([w.s([e1r, e1gt], 'jca', '( %s -> ( ( 1 + %s ) e. RR /\\ 1 < ( 1 + %s ) ) )' % (A0, EL, EL)), w.s([cdr], 'recnd', '( %s -> %s e. CC )' % (A0, CD))], 'jca',
               '( %s -> ( ( ( 1 + %s ) e. RR /\\ 1 < ( 1 + %s ) ) /\\ %s e. CC ) )' % (A0, EL, EL, CD)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAJAD))
# the derivative bound
dvj = w.s([w.s([w.s([w.s([w.s([sf], 'adantr', '( %s -> S : NN --> CC )' % Ajy), jn2], 'jca', '( %s -> ( S : NN --> CC /\\ j e. NN ) )' % Ajy), w.s([bo], 'adantr', '( %s -> %s e. %s )' % (Ajy, B_, TOP))],
                    'jca', '( %s -> ( ( S : NN --> CC /\\ j e. NN ) /\\ %s e. %s ) )' % (Ajy, B_, TOP)), w.inst('abtdv')], 'syl',
               '( %s -> ( CC _D %s ) = ( p e. %s |-> %s ) )' % (Ajy, INBP('j'), B_, DAT('S', 'j', 'p')))], 'idi', '( %s -> ( CC _D %s ) = ( p e. %s |-> %s ) )' % (Ajy, INBP('j'), B_, DAT('S', 'j', 'p')))
svj = w.s([w.s([abfv(w, Ajy, 'j', jn2)], 'oveq2d', '( %s -> ( CC _D ( %s ` j ) ) = ( CC _D %s ) )' % (Ajy, AB, INBP('j'))), dvj], 'eqtrd',
          '( %s -> ( CC _D ( %s ` j ) ) = ( p e. %s |-> %s ) )' % (Ajy, AB, B_, DAT('S', 'j', 'p')))
dvv = w.s([w.s([svj], 'fveq1d', '( %s -> ( ( CC _D ( %s ` j ) ) ` y ) = ( ( p e. %s |-> %s ) ` y ) )' % (Ajy, AB, B_, DAT('S', 'j', 'p'))), datval(w, Ajy, 'j', 'y', yb)], 'eqtrd',
          '( %s -> ( ( CC _D ( %s ` j ) ) ` y ) = %s )' % (Ajy, AB, DAT('S', 'j', 'y')))
KE1 = lambda k: '( %s ^c -u ( 1 + %s ) )' % (k, EL)
tb = w.s([pk, w.inst('abtdvb')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (Ajy, DAT('S', 'j', 'y'), CD, KE1('j')))
subr = w.s([w.s([], 'oveq1', '( n = j -> %s = %s )' % (KE1('n'), KE1('j')))], 'oveq2d', '( n = j -> ( %s x. %s ) = ( %s x. %s ) )' % (CD, KE1('n'), CD, KE1('j')))
rv = mpv(w, Ajy, MAJAD, 'j', '( %s x. %s )' % (CD, KE1('j')), subr, jn2, vexd(w, Ajy, '( %s x. %s )' % (CD, KE1('j'))))
db2 = w.s([w.s([w.s([dvv], 'fveq2d', '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) = ( abs ` %s ) )' % (Ajy, AB, DAT('S', 'j', 'y'))), tb], 'eqbrtrd',
                '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s x. %s ) )' % (Ajy, AB, CD, KE1('j'))), rv], 'breqtrrd',
          '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (Ajy, AB, MAJAD))
rb = w.s([db2], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (A0, B_, AB, MAJAD))
ud = w.s([rf, rcv, rb], '3jca', '( %s -> %s )' % (A0, UHD(AB, MAJAD, B_)))
w.qed([left, w.s([um, ud], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, UHM(AB, MAJA, B_), UHD(AB, MAJAD, B_)))], 'jca', '( %s -> %s )' % (A0, UH(AB, MAJA, MAJAD, B_)))
run5(w)

# ---------------------------------------------------------------- abbxhol
GS = GSUM(AB, B_)
AS = ASF('S', B_)
w = W('abbxhol', 'The Abel series of a bounded partial-sum sequence is holomorphic on every open box in the '
      'right half-plane ( ~ uhhol at ~ abbxuh ).')
A0 = BXA
hol = w.s([w.s([], 'abbxuh', '( %s -> %s )' % (A0, UH(AB, MAJA, MAJAD, B_))), w.inst('uhhol')], 'syl', '( %s -> %s )' % (A0, HOLG2(GS, B_)))
Azk = '( z e. %s /\\ k e. NN )' % B_
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Azk)
zb = w.s([], 'simpl', '( %s -> z e. %s )' % (Azk, B_))
vv = w.s([w.s([abfv(w, Azk, 'k', kn)], 'fveq1d', '( %s -> ( ( %s ` k ) ` z ) = ( %s ` z ) )' % (Azk, AB, INBP('k'))), atmval(w, Azk, 'k', 'z', zb)], 'eqtrd',
         '( %s -> ( ( %s ` k ) ` z ) = %s )' % (Azk, AB, ATM('S', 'k', 'z')))
ge = w.s([w.s([vv], 'sumeq2dv', '( z e. %s -> sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN %s )' % (B_, AB, ATM('S', 'k', 'z')))], 'mpteq2ia', '%s = %s' % (GS, AS))
b1 = w.s([ge], 'eleq1i', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (GS, B_, AS, B_))
b2 = w.s([w.s([w.s([ge], 'oveq2i', '( CC _D %s ) = ( CC _D %s )' % (GS, AS))], 'dmeqi', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (GS, AS))], 'sseq2i',
         '( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) )' % (B_, GS, B_, AS))
w.qed([hol, w.s([b1, b2], 'anbi12i', '( %s <-> %s )' % (HOLG2(GS, B_), HOLG2(AS, B_)))], 'sylib', '( %s -> %s )' % (A0, HOLG2(AS, B_)))
run5(w)

# ---------------------------------------------------------------- abhol
D = HP()
ASH = ASF('S', D)
w = W('abhol', 'The Abel series of a bounded partial-sum sequence is holomorphic on the open half-plane '
      '` ( Re ` z ) > T ` for every ` 0 <_ T ` : Lean\'s ` differentiableOn_Afun ` of LGrowth.lean, by boxes '
      '( ~ abbxhol ) and the locality of holomorphy ( ~ holloc ).')
A0 = '( %s /\\ ( T e. RR /\\ 0 <_ T ) )' % ABS
abs_ = w.s([], 'simpl', '( %s -> %s )' % (A0, ABS))
tt = w.s([], 'simpr', '( %s -> ( T e. RR /\\ 0 <_ T ) )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
t0 = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 0 <_ T )' % A0)
# G : HP T --> CC
Az = '( %s /\\ z e. %s )' % (A0, D)
bi = w.s([w.s([tr], 'adantr', '( %s -> T e. RR )' % Az), w.inst('elhp2')], 'syl', '( %s -> ( z e. %s <-> ( z e. CC /\\ T < ( Re ` z ) ) ) )' % (Az, D))
both = w.s([w.s([], 'simpr', '( %s -> z e. %s )' % (Az, D)), bi], 'mpbid', '( %s -> ( z e. CC /\\ T < ( Re ` z ) ) )' % Az)
zc = w.s([both], 'simpld', '( %s -> z e. CC )' % Az)
tz = w.s([both], 'simprd', '( %s -> T < ( Re ` z ) )' % Az)
z0 = w.s([a1(w, Az, '0re', '0 e. RR'), w.s([tr], 'adantr', '( %s -> T e. RR )' % Az), w.s([zc], 'recld', '( %s -> ( Re ` z ) e. RR )' % Az), w.s([t0], 'adantr', '( %s -> 0 <_ T )' % Az), tz], 'lelttrd',
         '( %s -> 0 < ( Re ` z ) )' % Az)
cl = w.s([w.s([w.s([abs_], 'adantr', '( %s -> %s )' % (Az, ABS)), w.s([zc, z0], 'jca', '( %s -> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % Az)], 'jca',
              '( %s -> ( %s /\\ ( z e. CC /\\ 0 < ( Re ` z ) ) ) )' % (Az, ABS)), w.inst('abcl')], 'syl', '( %s -> sum_ k e. NN %s e. CC )' % (Az, ATM('S', 'k', 'z')))
gf = w.s([cl, w.s([], 'eqid', '%s = %s' % (ASH, ASH))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, ASH, D))
hss = a1(w, A0, 'hpss', '%s C_ CC' % D)
# the local box at y
Ay = '( %s /\\ y e. %s )' % (A0, D)
biy = w.s([w.s([tr], 'adantr', '( %s -> T e. RR )' % Ay), w.inst('elhp2')], 'syl', '( %s -> ( y e. %s <-> ( y e. CC /\\ T < ( Re ` y ) ) ) )' % (Ay, D))
bothy = w.s([w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, D)), biy], 'mpbid', '( %s -> ( y e. CC /\\ T < ( Re ` y ) ) )' % Ay)
yc = w.s([bothy], 'simpld', '( %s -> y e. CC )' % Ay)
ty = w.s([bothy], 'simprd', '( %s -> T < ( Re ` y ) )' % Ay)
ry = w.s([yc], 'recld', '( %s -> ( Re ` y ) e. RR )' % Ay)
iy = w.s([yc], 'imcld', '( %s -> ( Im ` y ) e. RR )' % Ay)
try_ = w.s([tr], 'adantr', '( %s -> T e. RR )' % Ay)
t0y = w.s([t0], 'adantr', '( %s -> 0 <_ T )' % Ay)
L0 = '( ( T + ( Re ` y ) ) / 2 )'
R0 = '( ( abs ` y ) + 1 )'
BXY = BX(L0, R0)
ay = w.s([yc], 'abscld', '( %s -> ( abs ` y ) e. RR )' % Ay)
r0r = w.s([ay, a1(w, Ay, '1re', '1 e. RR')], 'readdcld', '( %s -> %s e. RR )' % (Ay, R0))
ry0 = w.s([a1(w, Ay, '0re', '0 e. RR'), try_, ry, t0y, ty], 'lelttrd', '( %s -> 0 < ( Re ` y ) )' % Ay)
try2 = w.s([try_, ry], 'readdcld', '( %s -> ( T + ( Re ` y ) ) e. RR )' % Ay)
l0rp = w.s([w.s([try2, w.s([try_, ry, t0y, ry0], 'addgegt0d', '( %s -> 0 < ( T + ( Re ` y ) ) )' % Ay)], 'elrpd', '( %s -> ( T + ( Re ` y ) ) e. RR+ )' % Ay)], 'rphalfcld', '( %s -> %s e. RR+ )' % (Ay, L0))
l0r = w.s([l0rp], 'rpred', '( %s -> %s e. RR )' % (Ay, L0))
# y e. BXY
l0lt = w.s([ty, w.s([try_, ry, w.inst('avglt2')], 'syl2anc', '( %s -> ( T < ( Re ` y ) <-> %s < ( Re ` y ) ) )' % (Ay, L0))], 'mpbid', '( %s -> %s < ( Re ` y ) )' % (Ay, L0))
ary = w.s([yc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` y ) ) <_ ( abs ` y ) )' % Ay)
aiy = w.s([yc, w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` y ) ) <_ ( abs ` y ) )' % Ay)
arylt = w.s([w.s([w.s([ry], 'recnd', '( %s -> ( Re ` y ) e. CC )' % Ay)], 'abscld', '( %s -> ( abs ` ( Re ` y ) ) e. RR )' % Ay), ay, r0r, ary, w.s([ay], 'ltp1d', '( %s -> ( abs ` y ) < %s )' % (Ay, R0))], 'lelttrd',
            '( %s -> ( abs ` ( Re ` y ) ) < %s )' % (Ay, R0))
aiylt = w.s([w.s([w.s([iy], 'recnd', '( %s -> ( Im ` y ) e. CC )' % Ay)], 'abscld', '( %s -> ( abs ` ( Im ` y ) ) e. RR )' % Ay), ay, r0r, aiy, w.s([ay], 'ltp1d', '( %s -> ( abs ` y ) < %s )' % (Ay, R0))], 'lelttrd',
            '( %s -> ( abs ` ( Im ` y ) ) < %s )' % (Ay, R0))
rypair = w.s([arylt, w.s([ry, r0r, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` ( Re ` y ) ) < %s <-> ( -u %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) ) )' % (Ay, R0, R0, R0))], 'mpbid',
             '( %s -> ( -u %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) )' % (Ay, R0, R0))
iypair = w.s([aiylt, w.s([iy, r0r, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` ( Im ` y ) ) < %s <-> ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) )' % (Ay, R0, R0, R0))], 'mpbid',
             '( %s -> ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) )' % (Ay, R0, R0))
inb = w.s([yc, w.s([l0lt, w.s([rypair], 'simprd', '( %s -> ( Re ` y ) < %s )' % (Ay, R0))], 'jca', '( %s -> ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) )' % (Ay, L0, R0)), iypair], '3jca',
          '( %s -> ( y e. CC /\\ ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) /\\ ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) )' % (Ay, L0, R0, R0, R0))
ybx = w.s([w.s([w.s([l0r, r0r], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (Ay, L0, R0)), inb], 'jca',
               '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( y e. CC /\\ ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) /\\ ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) ) )' % (Ay, L0, R0, L0, R0, R0, R0)),
           w.inst('elbxr')], 'syl', '( %s -> y e. %s )' % (Ay, BXY))
# BXY C_ HP T
Aw = '( %s /\\ w e. %s )' % (Ay, BXY)
inw = w.s([w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, BXY)), w.inst('elbxi')], 'syl',
          '( %s -> ( w e. CC /\\ ( %s < ( Re ` w ) /\\ ( Re ` w ) < %s ) /\\ ( -u %s < ( Im ` w ) /\\ ( Im ` w ) < %s ) ) )' % (Aw, L0, R0, R0, R0))
wc = w.s([inw, w.inst('simp1')], 'syl', '( %s -> w e. CC )' % Aw)
l0w = w.s([w.s([inw, w.inst('simp2')], 'syl', '( %s -> ( %s < ( Re ` w ) /\\ ( Re ` w ) < %s ) )' % (Aw, L0, R0))], 'simpld', '( %s -> %s < ( Re ` w ) )' % (Aw, L0))
tl0 = w.s([w.s([try_, ry, ty], 'ltled', '( %s -> T <_ ( Re ` y ) )' % Ay), w.s([try_, ry, w.inst('avgle1')], 'syl2anc', '( %s -> ( T <_ ( Re ` y ) <-> T <_ %s ) )' % (Ay, L0))], 'mpbid',
          '( %s -> T <_ %s )' % (Ay, L0))
tw = w.s([w.s([try_], 'adantr', '( %s -> T e. RR )' % Aw), w.s([l0r], 'adantr', '( %s -> %s e. RR )' % (Aw, L0)), w.s([wc], 'recld', '( %s -> ( Re ` w ) e. RR )' % Aw), w.s([tl0], 'adantr', '( %s -> T <_ %s )' % (Aw, L0)), l0w],
         'lelttrd', '( %s -> T < ( Re ` w ) )' % Aw)
whp = w.s([w.s([wc, tw], 'jca', '( %s -> ( w e. CC /\\ T < ( Re ` w ) ) )' % Aw), w.s([w.s([try_], 'adantr', '( %s -> T e. RR )' % Aw), w.inst('elhp2')], 'syl',
                                                                                    '( %s -> ( w e. %s <-> ( w e. CC /\\ T < ( Re ` w ) ) ) )' % (Aw, D))], 'mpbird', '( %s -> w e. %s )' % (Aw, D))
bss = w.s([w.s([whp], 'ex', '( %s -> ( w e. %s -> w e. %s ) )' % (Ay, BXY, D))], 'ssrdv', '( %s -> %s C_ %s )' % (Ay, BXY, D))
# BXY C_ dom ( CC _D ( G |` BXY ) )
ASB = ASF('S', BXY)
res = w.s([bss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (Ay, ASH, BXY, ASB))
bh = w.s([w.s([w.s([abs_], 'adantr', '( %s -> %s )' % (Ay, ABS)), w.s([l0rp, r0r], 'jca', '( %s -> ( %s e. RR+ /\\ %s e. RR ) )' % (Ay, L0, R0))], 'jca',
              '( %s -> ( %s /\\ ( %s e. RR+ /\\ %s e. RR ) ) )' % (Ay, ABS, L0, R0)), w.inst('abbxhol')], 'syl', '( %s -> %s )' % (Ay, HOLG2(ASB, BXY)))
dss = w.s([w.s([bh], 'simprd', '( %s -> %s C_ dom ( CC _D %s ) )' % (Ay, BXY, ASB)),
           w.s([w.s([res], 'oveq2d', '( %s -> ( CC _D ( %s |` %s ) ) = ( CC _D %s ) )' % (Ay, ASH, BXY, ASB))], 'dmeqd', '( %s -> dom ( CC _D ( %s |` %s ) ) = dom ( CC _D %s ) )' % (Ay, ASH, BXY, ASB))],
          'sseqtrrd', '( %s -> %s C_ dom ( CC _D ( %s |` %s ) ) )' % (Ay, BXY, ASH, BXY))
LOC = lambda u: '( y e. %s /\\ %s C_ %s /\\ %s C_ dom ( CC _D ( %s |` %s ) ) )' % (u, u, D, u, ASH, u)
sub = w.s([w.s([], 'eleq2', '( u = %s -> ( y e. u <-> y e. %s ) )' % (BXY, BXY)), w.s([], 'sseq1', '( u = %s -> ( u C_ %s <-> %s C_ %s ) )' % (BXY, D, BXY, D)),
           w.s([w.s([], 'id', '( u = %s -> u = %s )' % (BXY, BXY)), w.s([w.s([w.s([], 'reseq2', '( u = %s -> ( %s |` u ) = ( %s |` %s ) )' % (BXY, ASH, ASH, BXY))], 'oveq2d',
                                                                          '( u = %s -> ( CC _D ( %s |` u ) ) = ( CC _D ( %s |` %s ) ) )' % (BXY, ASH, ASH, BXY))], 'dmeqd',
                                                                     '( u = %s -> dom ( CC _D ( %s |` u ) ) = dom ( CC _D ( %s |` %s ) ) )' % (BXY, ASH, ASH, BXY))], 'sseq12d',
               '( u = %s -> ( u C_ dom ( CC _D ( %s |` u ) ) <-> %s C_ dom ( CC _D ( %s |` %s ) ) ) )' % (BXY, ASH, BXY, ASH, BXY))], '3anbi123d',
          '( u = %s -> ( %s <-> %s ) )' % (BXY, LOC('u'), LOC(BXY)))
bo = a1(w, Ay, 'bxopn', '%s e. %s' % (BXY, TOP))
rsp = w.s([sub], 'rspcev', '( ( %s e. %s /\\ %s ) -> E. u e. %s %s )' % (BXY, TOP, LOC(BXY), TOP, LOC('u')))
ex = w.s([w.s([bo, w.s([ybx, bss, dss], '3jca', '( %s -> %s )' % (Ay, LOC(BXY)))], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (Ay, BXY, TOP, LOC(BXY))), rsp], 'syl',
         '( %s -> E. u e. %s %s )' % (Ay, TOP, LOC('u')))
ral = w.s([ex], 'ralrimiva', '( %s -> A. y e. %s E. u e. %s %s )' % (A0, D, TOP, LOC('u')))
w.qed([w.s([w.s([gf, hss], 'jca', '( %s -> ( %s : %s --> CC /\\ %s C_ CC ) )' % (A0, ASH, D, D)), ral], 'jca',
           '( %s -> ( ( %s : %s --> CC /\\ %s C_ CC ) /\\ A. y e. %s E. u e. %s %s ) )' % (A0, ASH, D, D, D, TOP, LOC('u'))), w.inst('holloc')], 'syl', '( %s -> %s )' % (A0, HOLG2(ASH, D)))
run5(w)

# ---------------------------------------------------------------- lchrhol0
CSFV = CSF()
CATMZ = lambda k: '( %s x. ( ( %s ^c -u z ) - ( ( %s + 1 ) ^c -u z ) ) )' % (CSUM(k), k, k)
LC = '( z e. %s |-> sum_ k e. NN %s )' % (D, CATMZ('k'))
LCS = ASF(CSFV, D)
w = W('lchrhol0', 'The continued L-function of a nonprincipal Dirichlet character (its Abel series) is '
      'holomorphic on the open half-plane ` ( Re ` z ) > T ` for every ` 0 <_ T ` : Lean\'s '
      '` differentiable_LFunction ` on the right half-plane ( ~ abhol at ~ lchrcsf ).')
A0 = '( %s /\\ ( T e. RR /\\ 0 <_ T ) )' % CHR
chr_ = w.s([], 'simpl', '( %s -> %s )' % (A0, CHR))
tt = w.s([], 'simpr', '( %s -> ( T e. RR /\\ 0 <_ T ) )' % A0)
csf = w.s([chr_, w.inst('lchrcsf')], 'syl', '( %s -> ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) )' % (A0, CSFV, CSFV))
hol = w.s([w.s([csf, tt], 'jca', '( %s -> ( ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) /\\ ( T e. RR /\\ 0 <_ T ) ) )' % (A0, CSFV, CSFV)), w.inst('abhol')], 'syl',
          '( %s -> %s )' % (A0, HOLG2(LCS, D)))
Azk = '( ( %s /\\ z e. %s ) /\\ k e. NN )' % (A0, D)
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Azk)
sub = w.s([w.s([], 'oveq2', '( q = k -> ( 1 ... q ) = ( 1 ... k ) )')], 'sumeq1d', '( q = k -> %s = %s )' % (CSUM('q'), CSUM('k')))
cv = mpv(w, Azk, CSFV, 'k', CSUM('k'), sub, kn, vexd(w, Azk, CSUM('k'), 'sum'))
sm = w.s([w.s([cv], 'oveq1d', '( %s -> %s = %s )' % (Azk, ATM(CSFV, 'k', 'z'), CATMZ('k')))], 'sumeq2dv',
         '( ( %s /\\ z e. %s ) -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, D, ATM(CSFV, 'k', 'z'), CATMZ('k')))
eq = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A0, LCS, LC))
b1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A0, LCS, D, LC, D))
b2 = w.s([w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, LCS, LC))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, LCS, LC))], 'sseq2d',
         '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A0, D, LCS, D, LC))
w.qed([hol, w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A0, HOLG2(LCS, D), HOLG2(LC, D)))], 'mpbid', '( %s -> %s )' % (A0, HOLG2(LC, D)))
run5(w)
