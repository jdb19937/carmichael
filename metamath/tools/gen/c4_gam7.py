"""C4, Gamma block 7: a uniform constant on the abscissa range, and the frozen
strip bound."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import num
from lin import linarith


def rlit(w, A, t, k):
    return w.s([num.fact(w, t, k)], 'a1i', '( %s -> %s )' %
               (A, {'RR': '%s e. RR', 'RR+': '%s e. RR+', 'CC': '%s e. CC',
                    'NN0': '%s e. NN0', 'NN': '%s e. NN', 'ZZ': '%s e. ZZ', 'ne0': '%s =/= 0',
                    'ge0': '0 <_ %s', 'gt0': '0 < %s'}[k] % t))


R100 = '; ; 1 0 0'
EPS = '( 1 / %s )' % R100
UU = '{ a e. CC | ( ( abs ` a ) <_ %s /\\ A. b e. NN0 %s <_ ( abs ` ( a + b ) ) ) }' % (R100, EPS)
GG = '( g e. NN |-> ( c e. %s |-> ( ( c x. ( log ` ( ( g + 1 ) / g ) ) ) - ( log ` ( ( c / g ) + 1 ) ) ) ) )' % UU
ICC = '( %s [,] 3 )' % EPS
UB = '( ( abs ` p ) <_ %s /\\ A. b e. NN0 %s <_ ( abs ` ( p + b ) ) )' % (R100, EPS)

# ---------------------------------------------------------------- gamubq
AQ = '( P e. RR /\\ %s <_ P )' % EPS
w = W('gamubq', 'A real number at least ` ( 1 / ; ; 1 0 0 ) ` stays at that distance '
      'from every nonpositive integer: the hypothesis of ~ lgambdd at ` R = ; ; 1 0 0 `.')
prr = w.s([], 'simpl', '( %s -> P e. RR )' % AQ)
pge = w.s([], 'simpr', '( %s -> %s <_ P )' % (AQ, EPS))
AB = '( %s /\\ b e. NN0 )' % AQ
br = w.s([w.s([], 'simpr', '( %s -> b e. NN0 )' % AB), w.inst('nn0re')], 'syl', '( %s -> b e. RR )' % AB)
b0 = w.s([w.s([], 'simpr', '( %s -> b e. NN0 )' % AB), w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ b )' % AB)
pr2 = w.s([prr], 'adantr', '( %s -> P e. RR )' % AB)
pge2 = w.s([pge], 'adantr', '( %s -> %s <_ P )' % (AB, EPS))
pb = w.s([pr2, br], 'readdcld', '( %s -> ( P + b ) e. RR )' % AB)
pb0 = linarith(w, AB, [b0, pge2], '0 <_ ( P + b )', leaves={'P': pr2, 'b': br})
abpb = w.s([pb, pb0], 'absidd', '( %s -> ( abs ` ( P + b ) ) = ( P + b ) )' % AB)
ge = linarith(w, AB, [b0, pge2], '%s <_ ( P + b )' % EPS, leaves={'P': pr2, 'b': br})
gek = w.s([ge, w.s([abpb], 'eqcomd', '( %s -> ( P + b ) = ( abs ` ( P + b ) ) )' % AB)], 'breqtrd',
          '( %s -> %s <_ ( abs ` ( P + b ) ) )' % (AB, EPS))
w.qed([gek], 'ralrimiva', '( %s -> A. b e. NN0 %s <_ ( abs ` ( P + b ) ) )' % (AQ, EPS))
run4(w)

# ---------------------------------------------------------------- gamrbd
w = W('gamrbd', 'The gamma function is bounded on the real interval '
      '` ( ( 1 / ; 1 0 0 ) [,] 3 ) `: its logarithm is bounded on the set of '
      '~ lgambdd at ` R = ; 1 0 0 `, which contains that interval.')
A = '%s e. NN' % R100
rn = w.s([], 'id', '( %s -> %s )' % (A, A))
ueq = w.s([], 'eqid', '%s = %s' % (UU, UU))
geq = w.s([], 'eqid', '%s = %s' % (GG, GG))
bdd = w.s([rn, ueq, geq], 'lgambdd', '( %s -> E. r e. RR A. c e. %s ( abs ` ( log_G ` c ) ) <_ r )' % (A, UU))
AR = '( %s /\\ ( r e. RR /\\ A. c e. %s ( abs ` ( log_G ` c ) ) <_ r ) )' % (A, UU)
pairs = w.s([], 'simpr', '( %s -> ( r e. RR /\\ A. c e. %s ( abs ` ( log_G ` c ) ) <_ r ) )' % (AR, UU))
rr = w.s([pairs, w.inst('simpl')], 'syl', '( %s -> r e. RR )' % AR)
rall = w.s([pairs, w.inst('simpr')], 'syl', '( %s -> A. c e. %s ( abs ` ( log_G ` c ) ) <_ r )' % (AR, UU))
erp = w.s([rr, w.inst('rpefcl')], 'syl', '( %s -> ( exp ` r ) e. RR+ )' % AR)
AP = '( %s /\\ p e. %s )' % (AR, ICC)
pm = w.s([], 'simpr', '( %s -> p e. %s )' % (AP, ICC))
e2 = w.s([rlit(w, AP, EPS, 'RR'), rlit(w, AP, '3', 'RR'), w.inst('elicc2')], 'syl2anc',
         '( %s -> ( p e. %s <-> ( p e. RR /\\ %s <_ p /\\ p <_ 3 ) ) )' % (AP, ICC, EPS))
pin = w.s([pm, e2], 'mpbid', '( %s -> ( p e. RR /\\ %s <_ p /\\ p <_ 3 ) )' % (AP, EPS))
pr = w.s([pin, w.inst('simp1')], 'syl', '( %s -> p e. RR )' % AP)
pge = w.s([pin, w.inst('simp2')], 'syl', '( %s -> %s <_ p )' % (AP, EPS))
ple = w.s([pin, w.inst('simp3')], 'syl', '( %s -> p <_ 3 )' % AP)
p0 = linarith(w, AP, [pge], '0 < p', leaves={'p': pr})
prp = w.s([pr, p0], 'elrpd', '( %s -> p e. RR+ )' % AP)
pc = w.s([pr], 'recnd', '( %s -> p e. CC )' % AP)
abp = w.s([pr, w.s([p0], 'ltled', '( %s -> 0 <_ p )' % AP)], 'absidd', '( %s -> ( abs ` p ) = p )' % AP)
p100 = linarith(w, AP, [ple], 'p <_ %s' % R100, leaves={'p': pr})
ab100 = w.s([abp, p100], 'eqbrtrd', '( %s -> ( abs ` p ) <_ %s )' % (AP, R100))
quant = w.s([w.s([pr, pge], 'jca', '( %s -> ( p e. RR /\\ %s <_ p ) )' % (AP, EPS)), w.inst('gamubq')],
            'syl', '( %s -> A. b e. NN0 %s <_ ( abs ` ( p + b ) ) )' % (AP, EPS))
# p e. UU
s1 = w.s([w.s([], 'fveq2', '( a = p -> ( abs ` a ) = ( abs ` p ) )')], 'breq1d',
         '( a = p -> ( ( abs ` a ) <_ %s <-> ( abs ` p ) <_ %s ) )' % (R100, R100))
s2 = w.s([w.s([w.s([], 'oveq1', '( a = p -> ( a + b ) = ( p + b ) )')], 'fveq2d',
              '( a = p -> ( abs ` ( a + b ) ) = ( abs ` ( p + b ) ) )')], 'breq2d',
         '( a = p -> ( %s <_ ( abs ` ( a + b ) ) <-> %s <_ ( abs ` ( p + b ) ) ) )' % (EPS, EPS))
s3 = w.s([s2], 'ralbidv', '( a = p -> ( A. b e. NN0 %s <_ ( abs ` ( a + b ) ) <-> A. b e. NN0 %s <_ ( abs ` ( p + b ) ) ) )' % (EPS, EPS))
s4 = w.s([s1, s3], 'anbi12d',
         '( a = p -> ( ( ( abs ` a ) <_ %s /\\ A. b e. NN0 %s <_ ( abs ` ( a + b ) ) ) <-> %s ) )' % (R100, EPS, UB))
mem = w.s([pc, w.s([ab100, quant], 'jca', '( %s -> %s )' % (AP, UB)),
           w.s([s4], 'elrab', '( p e. %s <-> ( p e. CC /\\ %s ) )' % (UU, UB))], 'sylanbrc',
          '( %s -> p e. %s )' % (AP, UU))
# the bound
lgsub = w.s([w.s([w.s([], 'fveq2', '( c = p -> ( log_G ` c ) = ( log_G ` p ) )')], 'fveq2d',
                 '( c = p -> ( abs ` ( log_G ` c ) ) = ( abs ` ( log_G ` p ) ) )')], 'breq1d',
            '( c = p -> ( ( abs ` ( log_G ` c ) ) <_ r <-> ( abs ` ( log_G ` p ) ) <_ r ) )')
lg = w.s([lgsub, w.s([rall], 'adantr', '( %s -> A. c e. %s ( abs ` ( log_G ` c ) ) <_ r )' % (AP, UU)), mem],
         'rspcdva', '( %s -> ( abs ` ( log_G ` p ) ) <_ r )' % AP)
# ( _G ` p ) = ( exp ` ( log_G ` p ) )
dm = w.s([w.s([pr, p0], 'jca', '( %s -> ( p e. RR /\\ 0 < p ) )' % AP), w.inst('gamrrp')], 'syl',
         '( %s -> ( _G ` p ) e. RR+ )' % AP)
dgd = w.s([w.s([pc, w.s([abp, p100], 'eqbrtrd', 'dummy')], 'jca', 'dummy')], 'id', 'x')
w.lines.pop(); w.lines.pop(); w.lines.pop()
dnn = w.s([w.s([pc, p0], 'jca', '( %s -> ( p e. CC /\\ 0 < ( Re ` p ) ) )' % AP)], 'id', 'x')
w.lines.pop(); w.lines.pop()
pre = w.s([pr], 'rered', '( %s -> ( Re ` p ) = p )' % AP)
dnn = w.s([w.s([pc, w.s([p0, pre], 'breqtrrd', '( %s -> 0 < ( Re ` p ) )' % AP)], 'jca',
                '( %s -> ( p e. CC /\\ 0 < ( Re ` p ) ) )' % AP), w.inst('zrenn')], 'syl',
          '( %s -> p e. ( CC \\ ( ZZ \\ NN ) ) )' % AP)
lgf = w.s([w.s([], 'lgamf', 'log_G : ( CC \\ ( ZZ \\ NN ) ) --> CC')], 'a1i',
          '( %s -> log_G : ( CC \\ ( ZZ \\ NN ) ) --> CC )' % AP)
fco = w.s([lgf, dnn, w.inst('fvco3')], 'syl2anc', '( %s -> ( ( exp o. log_G ) ` p ) = ( exp ` ( log_G ` p ) ) )' % AP)
dg = w.s([w.s([w.s([], 'df-gam', '_G = ( exp o. log_G )')], 'a1i', '( %s -> _G = ( exp o. log_G ) )' % AP)], 'fveq1d',
         '( %s -> ( _G ` p ) = ( ( exp o. log_G ) ` p ) )' % AP)
gval = w.s([dg, fco], 'eqtrd', '( %s -> ( _G ` p ) = ( exp ` ( log_G ` p ) ) )' % AP)
lgc = w.s([dnn, w.inst('lgamcl')], 'syl', '( %s -> ( log_G ` p ) e. CC )' % AP)
aef = w.s([lgc, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` ( log_G ` p ) ) ) = ( exp ` ( Re ` ( log_G ` p ) ) ) )' % AP)
gabs = w.s([w.s([dm], 'rpred', '( %s -> ( _G ` p ) e. RR )' % AP),
            w.s([dm], 'rpge0d', '( %s -> 0 <_ ( _G ` p ) )' % AP)], 'absidd',
           '( %s -> ( abs ` ( _G ` p ) ) = ( _G ` p ) )' % AP)
chain = w.s([w.s([gval], 'fveq2d', '( %s -> ( abs ` ( _G ` p ) ) = ( abs ` ( exp ` ( log_G ` p ) ) ) )' % AP), aef],
            'eqtrd', '( %s -> ( abs ` ( _G ` p ) ) = ( exp ` ( Re ` ( log_G ` p ) ) ) )' % AP)
rel = w.s([lgc, w.inst('releabs')], 'syl', '( %s -> ( Re ` ( log_G ` p ) ) <_ ( abs ` ( log_G ` p ) ) )' % AP)
retr = w.s([w.s([lgc], 'recld', '( %s -> ( Re ` ( log_G ` p ) ) e. RR )' % AP),
            w.s([lgc], 'abscld', '( %s -> ( abs ` ( log_G ` p ) ) e. RR )' % AP),
            w.s([rr], 'adantr', '( %s -> r e. RR )' % AP), rel, lg], 'letrd',
           '( %s -> ( Re ` ( log_G ` p ) ) <_ r )' % AP)
efle = w.s([w.s([lgc], 'recld', '( %s -> ( Re ` ( log_G ` p ) ) e. RR )' % AP),
            w.s([rr], 'adantr', '( %s -> r e. RR )' % AP), w.inst('efle')], 'syl2anc',
           '( %s -> ( ( Re ` ( log_G ` p ) ) <_ r <-> ( exp ` ( Re ` ( log_G ` p ) ) ) <_ ( exp ` r ) ) )' % AP)
fin = w.s([w.s([gabs], 'eqcomd', '( %s -> ( _G ` p ) = ( abs ` ( _G ` p ) ) )' % AP),
           w.s([chain, w.s([retr, efle], 'mpbid', '( %s -> ( exp ` ( Re ` ( log_G ` p ) ) ) <_ ( exp ` r ) )' % AP)],
               'eqbrtrd', '( %s -> ( abs ` ( _G ` p ) ) <_ ( exp ` r ) )' % AP)],
          'eqbrtrd', '( %s -> ( _G ` p ) <_ ( exp ` r ) )' % AP)
allp = w.s([fin], 'ralrimiva', '( %s -> A. p e. %s ( _G ` p ) <_ ( exp ` r ) )' % (AR, ICC))
sub2 = w.s([w.s([w.s([], 'breq2', '( q = ( exp ` r ) -> ( ( _G ` p ) <_ q <-> ( _G ` p ) <_ ( exp ` r ) ) )')],
                'ralbidv', '( q = ( exp ` r ) -> ( A. p e. %s ( _G ` p ) <_ q <-> A. p e. %s ( _G ` p ) <_ ( exp ` r ) ) )' % (ICC, ICC))],
           'adantl', '( ( %s /\\ q = ( exp ` r ) ) -> ( A. p e. %s ( _G ` p ) <_ q <-> A. p e. %s ( _G ` p ) <_ ( exp ` r ) ) )' % (AR, ICC, ICC))
concl = 'E. q e. RR+ A. p e. %s ( _G ` p ) <_ q' % ICC
exq = w.s([erp, sub2, allp], 'rspcedvd', '( %s -> %s )' % (AR, concl))
lim = w.s([exq], 'rexlimdvaa',
          '( %s -> ( E. r e. RR A. c e. %s ( abs ` ( log_G ` c ) ) <_ r -> %s ) )' % (A, UU, concl))
mp = w.s([bdd, lim], 'mpd', '( %s -> %s )' % (A, concl))
w.qed([num.fact(w, R100, 'NN'), mp], 'mpan' if False else 'ax-mp', concl)
run4(w)

# ---------------------------------------------------------------- gamstrb
RD = '( Re ` d )'
VD = '( abs ` ( Im ` d ) )'
TD = '( 2 ^c -u ( %s / 2 ) )' % VD
CONC = 'E. h e. RR+ A. d e. CC ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( h x. %s ) )' % (EPS, RD, RD, TD)
w = W('gamstrb', 'The frozen strip bound: on ` ( 1 / ; ; 1 0 0 ) <_ ( Re ` z ) <_ 3 ` '
      'the gamma function is at most an absolute constant times '
      '` 2 ^c -u ( ( abs ` ( Im ` z ) ) / 2 ) `.  This is the form the explicit '
      'formula consumes; ~ gamvb has the sharp constant ` ; 1 6 ( _G ` ( Re ` z ) ) `.')
AA = '( q e. RR+ /\\ A. p e. %s ( _G ` p ) <_ q )' % ICC
qrp = w.s([], 'simpl', '( %s -> q e. RR+ )' % AA)
qall = w.s([], 'simpr', '( %s -> A. p e. %s ( _G ` p ) <_ q )' % (AA, ICC))
r16 = w.s([num.fact(w, '; 1 6', 'RR+')], 'a1i', '( %s -> ; 1 6 e. RR+ )' % AA)
prod = w.s([r16, qrp], 'rpmulcld', '( %s -> ( ; 1 6 x. q ) e. RR+ )' % AA)
AD = '( %s /\\ d e. CC )' % AA
AE = '( %s /\\ ( %s <_ %s /\\ %s <_ 3 ) )' % (AD, EPS, RD, RD)
dc = w.s([], 'simpr', '( %s -> d e. CC )' % AD)
dc2 = w.s([dc], 'adantr', '( %s -> d e. CC )' % AE)
lo = w.s([w.s([], 'simpr', '( %s -> ( %s <_ %s /\\ %s <_ 3 ) )' % (AE, EPS, RD, RD)), w.inst('simpl')], 'syl',
         '( %s -> %s <_ %s )' % (AE, EPS, RD))
hi = w.s([w.s([], 'simpr', '( %s -> ( %s <_ %s /\\ %s <_ 3 ) )' % (AE, EPS, RD, RD)), w.inst('simpr')], 'syl',
         '( %s -> %s <_ 3 )' % (AE, RD))
rdr = w.s([dc2], 'recld', '( %s -> %s e. RR )' % (AE, RD))
rd0 = linarith(w, AE, [lo], '0 < %s' % RD, leaves={RD: rdr})
vb = w.s([dc2, rd0, hi, w.inst('gamvb')], 'syl3anc',
         '( %s -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) )' % (AE, RD, TD))
# ( Re ` d ) e. ICC, so ( _G ` ( Re ` d ) ) <_ q
eicc = w.s([rlit(w, AE, EPS, 'RR'), rlit(w, AE, '3', 'RR'), w.inst('elicc2')], 'syl2anc',
           '( %s -> ( %s e. %s <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ 3 ) ) )' % (AE, RD, ICC, RD, EPS, RD, RD))
mem = w.s([w.s([rdr, lo, hi], 'jca3' if False else '3jca',
               '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ 3 ) )' % (AE, RD, EPS, RD, RD)), eicc], 'mpbird',
          '( %s -> %s e. %s )' % (AE, RD, ICC))
gsub = w.s([w.s([], 'fveq2', '( p = %s -> ( _G ` p ) = ( _G ` %s ) )' % (RD, RD))], 'breq1d',
           '( p = %s -> ( ( _G ` p ) <_ q <-> ( _G ` %s ) <_ q ) )' % (RD, RD))
gle = w.s([gsub, w.s([w.s([qall], 'adantr', '( %s -> A. p e. %s ( _G ` p ) <_ q )' % (AD, ICC))], 'adantr',
                     '( %s -> A. p e. %s ( _G ` p ) <_ q )' % (AE, ICC)), mem], 'rspcdva',
          '( %s -> ( _G ` %s ) <_ q )' % (AE, RD))
grp = w.s([w.s([rdr, rd0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (AE, RD, RD)), w.inst('gamrrp')], 'syl',
          '( %s -> ( _G ` %s ) e. RR+ )' % (AE, RD))
qr = w.s([w.s([qrp], 'adantr', '( %s -> q e. RR+ )' % AD)], 'adantr', '( %s -> q e. RR+ )' % AE)
r16e = w.s([num.fact(w, '; 1 6', 'RR+')], 'a1i', '( %s -> ; 1 6 e. RR+ )' % AE)
r16r = w.s([r16e], 'rpred', '( %s -> ; 1 6 e. RR )' % AE)
m1 = w.s([w.s([grp], 'rpred', '( %s -> ( _G ` %s ) e. RR )' % (AE, RD)), w.s([qr], 'rpred', '( %s -> q e. RR )' % AE),
          w.s([r16e], 'rpred', '( %s -> ; 1 6 e. RR )' % AE), w.s([r16e], 'rpge0d', '( %s -> 0 <_ ; 1 6 )' % AE), gle],
         'lemul2ad', '( %s -> ( ; 1 6 x. ( _G ` %s ) ) <_ ( ; 1 6 x. q ) )' % (AE, RD))
# the exponential factor
vdr = w.s([w.s([w.s([dc2], 'imcld', '( %s -> ( Im ` d ) e. RR )' % AE)], 'recnd', '( %s -> ( Im ` d ) e. CC )' % AE)],
          'abscld', '( %s -> %s e. RR )' % (AE, VD))
tdrp = w.s([rlit(w, AE, '2', 'RR+'),
            w.s([w.s([vdr, rlit(w, AE, '2', 'RR'), rlit(w, AE, '2', 'ne0')], 'redivcld',
                     '( %s -> ( %s / 2 ) e. RR )' % (AE, VD))], 'renegcld', '( %s -> -u ( %s / 2 ) e. RR )' % (AE, VD))],
           'rpcxpcld', '( %s -> %s e. RR+ )' % (AE, TD))
m2 = w.s([w.s([r16r, w.s([grp], 'rpred', '( %s -> ( _G ` %s ) e. RR )' % (AE, RD))], 'remulcld',
              '( %s -> ( ; 1 6 x. ( _G ` %s ) ) e. RR )' % (AE, RD)),
          w.s([w.s([r16e, qr], 'rpmulcld', '( %s -> ( ; 1 6 x. q ) e. RR+ )' % AE)], 'rpred',
              '( %s -> ( ; 1 6 x. q ) e. RR )' % AE),
          w.s([tdrp], 'rpred', '( %s -> %s e. RR )' % (AE, TD)), w.s([tdrp], 'rpge0d', '( %s -> 0 <_ %s )' % (AE, TD)),
          m1], 'lemul1ad',
         '( %s -> ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) <_ ( ( ; 1 6 x. q ) x. %s ) )' % (AE, RD, TD, TD))
fin = w.s([w.s([dc2], 'abscld', 'dummy')], 'id', 'x')
w.lines.pop(); w.lines.pop()
dgcl = w.s([w.s([w.s([dc2, rd0], 'jca', '( %s -> ( d e. CC /\\ 0 < %s ) )' % (AE, RD)), w.inst('zrenn')], 'syl',
                '( %s -> d e. ( CC \\ ( ZZ \\ NN ) ) )' % AE), w.inst('gamcl')], 'syl',
           '( %s -> ( _G ` d ) e. CC )' % AE)
tr = w.s([w.s([dgcl], 'abscld', '( %s -> ( abs ` ( _G ` d ) ) e. RR )' % AE),
          w.s([w.s([r16r, w.s([grp], 'rpred', '( %s -> ( _G ` %s ) e. RR )' % (AE, RD))], 'remulcld',
                   '( %s -> ( ; 1 6 x. ( _G ` %s ) ) e. RR )' % (AE, RD)),
               w.s([tdrp], 'rpred', '( %s -> %s e. RR )' % (AE, TD))], 'remulcld',
              '( %s -> ( ( ; 1 6 x. ( _G ` %s ) ) x. %s ) e. RR )' % (AE, RD, TD)),
          w.s([w.s([w.s([r16e, qr], 'rpmulcld', '( %s -> ( ; 1 6 x. q ) e. RR+ )' % AE)], 'rpred',
                   '( %s -> ( ; 1 6 x. q ) e. RR )' % AE),
               w.s([tdrp], 'rpred', '( %s -> %s e. RR )' % (AE, TD))], 'remulcld',
              '( %s -> ( ( ; 1 6 x. q ) x. %s ) e. RR )' % (AE, TD)), vb, m2], 'letrd',
         '( %s -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) )' % (AE, TD))
imp = w.s([tr], 'ex', '( %s -> ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) ) )' % (AD, EPS, RD, RD, TD))
alld = w.s([imp], 'ralrimiva',
           '( %s -> A. d e. CC ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) ) )' % (AA, EPS, RD, RD, TD))
hsub = w.s([w.s([w.s([], 'oveq1', '( h = ( ; 1 6 x. q ) -> ( h x. %s ) = ( ( ; 1 6 x. q ) x. %s ) )' % (TD, TD))],
                'breq2d', '( h = ( ; 1 6 x. q ) -> ( ( abs ` ( _G ` d ) ) <_ ( h x. %s ) <-> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) ) )' % (TD, TD))],
           'imbi2d', '( h = ( ; 1 6 x. q ) -> ( ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( h x. %s ) ) <-> ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) ) ) )' % (EPS, RD, RD, TD, EPS, RD, RD, TD))
hsub2 = w.s([hsub], 'ralbidv',
            '( h = ( ; 1 6 x. q ) -> ( A. d e. CC ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( h x. %s ) ) <-> A. d e. CC ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) ) ) )' % (EPS, RD, RD, TD, EPS, RD, RD, TD))
ex = w.s([prod, w.s([hsub2], 'adantl',
                    '( ( %s /\\ h = ( ; 1 6 x. q ) ) -> ( A. d e. CC ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( h x. %s ) ) <-> A. d e. CC ( ( %s <_ %s /\\ %s <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ( ; 1 6 x. q ) x. %s ) ) ) )' % (AA, EPS, RD, RD, TD, EPS, RD, RD, TD)),
          alld], 'rspcedvd', '( %s -> %s )' % (AA, CONC))
lim = w.s([ex], 'rexlimiva', '( E. q e. RR+ A. p e. %s ( _G ` p ) <_ q -> %s )' % (ICC, CONC))
w.qed([w.s([], 'gamrbd', 'E. q e. RR+ A. p e. %s ( _G ` p ) <_ q' % ICC), lim], 'ax-mp', CONC)
run4(w)
