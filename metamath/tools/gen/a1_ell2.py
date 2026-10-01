"""Sortie A1: the two remaining ell2/ell3 theorems of the blueprint, the
threshold for 1 <_ ell2 n and the divergence of C * ell2 n * ell3 n."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

E2 = lambda N: '( ell2 ` %s )' % N
E3 = lambda N: '( ell3 ` %s )' % N
LG = lambda X: '( log ` %s )' % X

# ---------------------------------------------------------------- ell2ge1b
PH = 'N e. ( ZZ>= ` 2 )'
w = W('ell2ge1b', 'The threshold for 1 <_ ell2 N: the logarithm of the logarithm reaches 1 exactly when N reaches ( exp ` _e ).')
i0 = w.s([], 'id', '( %s -> %s )' % (PH, PH))
nn = w.s([i0, w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % PH)
n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % PH)
nrp = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % PH)
lgre = w.s([nrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (PH, LG('N')))
gt1 = w.s([i0, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < N )' % PH)
bpos = w.s([nrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < %s <-> 1 < N ) )' % (PH, LG('N')))
lgpos = w.s([gt1, bpos], 'mpbird', '( %s -> 0 < %s )' % (PH, LG('N')))
lgrp = w.s([lgre, lgpos], 'elrpd', '( %s -> %s e. RR+ )' % (PH, LG('N')))
epr = w.s([w.s([], 'epr', '_e e. RR+')], 'a1i', '( %s -> _e e. RR+ )' % PH)
ere = w.s([w.s([], 'ere', '_e e. RR')], 'a1i', '( %s -> _e e. RR )' % PH)
b1 = w.s([epr, lgrp, w.inst('logleb')], 'syl2anc', '( %s -> ( _e <_ %s <-> %s <_ %s ) )' % (PH, LG('N'), LG('_e'), LG(LG('N'))))
le = w.s([w.s([], 'loge', '%s = 1' % LG('_e'))], 'a1i', '( %s -> %s = 1 )' % (PH, LG('_e')))
b2 = w.s([le], 'breq1d', '( %s -> ( %s <_ %s <-> 1 <_ %s ) )' % (PH, LG('_e'), LG(LG('N')), LG(LG('N'))))
ev = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = %s )' % (PH, E2('N'), LG(LG('N'))))
b3 = w.s([ev], 'breq2d', '( %s -> ( 1 <_ %s <-> 1 <_ %s ) )' % (PH, E2('N'), LG(LG('N'))))
b12 = w.s([b1, b2], 'bitrd', '( %s -> ( _e <_ %s <-> 1 <_ %s ) )' % (PH, LG('N'), LG(LG('N'))))
bl = w.s([b3, b12], 'bitr4d', '( %s -> ( 1 <_ %s <-> _e <_ %s ) )' % (PH, E2('N'), LG('N')))
b4 = w.s([ere, lgre, w.inst('efle')], 'syl2anc', '( %s -> ( _e <_ %s <-> ( exp ` _e ) <_ ( exp ` %s ) ) )' % (PH, LG('N'), LG('N')))
rl = w.s([nrp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = N )' % (PH, LG('N')))
b5 = w.s([rl], 'breq2d', '( %s -> ( ( exp ` _e ) <_ ( exp ` %s ) <-> ( exp ` _e ) <_ N ) )' % (PH, LG('N')))
b45 = w.s([b4, b5], 'bitrd', '( %s -> ( _e <_ %s <-> ( exp ` _e ) <_ N ) )' % (PH, LG('N')))
w.qed([bl, b45], 'bitrd', '( %s -> ( 1 <_ %s <-> ( exp ` _e ) <_ N ) )' % (PH, E2('N')))
run(w)

# ---------------------------------------------------------------- zrealge
ZR = lambda X: '( ( C x. %s ) x. %s )' % (E2(X), E3(X))
A3 = '( C e. RR /\\ 0 < C /\\ B e. RR )'
ABC = '( abs ` ( B / C ) )'
B2 = lambda X: '%s <_ %s' % (ABC, E2(X))
B3 = lambda X: '1 <_ %s' % E3(X)
H2 = 'A. i e. ( ZZ>= ` k ) %s' % B2('i')
H3 = 'A. j e. ( ZZ>= ` l ) %s' % B3('j')
KL = '( ( k + l ) + 3 )'
GOAL = 'E. m e. NN0 A. n e. ( ZZ>= ` m ) B <_ %s' % ZR('n')

w = W('zrealge', 'The product C * ell2 n * ell3 n tends to infinity for positive C: every real bound is eventually exceeded (Lean: tendsto_zreal in Step2W.lean).')


def a3parts(ante, a):
    return (w.s([a], 'simp1d', '( %s -> C e. RR )' % ante),
            w.s([a], 'simp2d', '( %s -> 0 < C )' % ante),
            w.s([a], 'simp3d', '( %s -> B e. RR )' % ante))


def abcsteps(ante, cr, c0, br):
    crp = w.s([cr, c0], 'elrpd', '( %s -> C e. RR+ )' % ante)
    bc = w.s([br, crp], 'rerpdivcld', '( %s -> ( B / C ) e. RR )' % ante)
    bcc = w.s([bc], 'recnd', '( %s -> ( B / C ) e. CC )' % ante)
    ab = w.s([bcc], 'abscld', '( %s -> %s e. RR )' % (ante, ABC))
    ge = w.s([bc], 'leabsd', '( %s -> ( B / C ) <_ %s )' % (ante, ABC))
    g0 = w.s([bcc], 'absge0d', '( %s -> 0 <_ %s )' % (ante, ABC))
    return crp, bc, ab, ge, g0


def rename(raw, ante, BND, FN, dum, outer, H):
    """from ( ante -> E. m e. NN0 A. n e. ( ZZ>= ` m ) BND(n) ) to
    ( ante -> E. outer e. NN0 A. dum e. ( ZZ>= ` outer ) BND(dum) )"""
    f1 = w.s([], 'fveq2', '( n = %s -> ( %s ` n ) = ( %s ` %s ) )' % (dum, FN, FN, dum))
    b1 = w.s([f1], 'breq2d', '( n = %s -> ( %s <-> %s ) )' % (dum, BND('n'), BND(dum)))
    c1 = w.s([b1], 'cbvralvw', '( A. n e. ( ZZ>= ` m ) %s <-> A. %s e. ( ZZ>= ` m ) %s )' % (BND('n'), dum, BND(dum)))
    c1d = w.s([c1], 'a1i', '( m = %s -> ( A. n e. ( ZZ>= ` m ) %s <-> A. %s e. ( ZZ>= ` m ) %s ) )' % (outer, BND('n'), dum, BND(dum)))
    f2 = w.s([], 'fveq2', '( m = %s -> ( ZZ>= ` m ) = ( ZZ>= ` %s ) )' % (outer, outer))
    c2 = w.s([f2], 'raleqdv', '( m = %s -> ( A. %s e. ( ZZ>= ` m ) %s <-> %s ) )' % (outer, dum, BND(dum), H))
    c3 = w.s([c1d, c2], 'bitrd', '( m = %s -> ( A. n e. ( ZZ>= ` m ) %s <-> %s ) )' % (outer, BND('n'), H))
    cb = w.s([c3], 'cbvrexvw', '( E. m e. NN0 A. n e. ( ZZ>= ` m ) %s <-> E. %s e. NN0 %s )' % (BND('n'), outer, H))
    return w.s([raw, cb], 'sylib', '( %s -> E. %s e. NN0 %s )' % (ante, outer, H))


i0 = w.s([], 'id', '( %s -> %s )' % (A3, A3))
cr, c0, br = a3parts(A3, i0)
crp, bc, ab, ge, g0 = abcsteps(A3, cr, c0, br)
e2raw = w.s([ab, w.inst('ell2ge')], 'syl', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (A3, B2('n')))
ex2 = rename(e2raw, A3, B2, 'ell2', 'i', 'k', H2)
one = w.s([], '1red', '( %s -> 1 e. RR )' % A3)
e3raw = w.s([one, w.inst('ell3ge')], 'syl', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (A3, B3('n')))
ex3 = rename(e3raw, A3, B3, 'ell3', 'j', 'l', H3)

P1 = '( ( %s /\\ k e. NN0 ) /\\ %s )' % (A3, H2)
P = '( ( %s /\\ l e. NN0 ) /\\ %s )' % (P1, H3)
Q = '( %s /\\ n e. ( ZZ>= ` %s ) )' % (P, KL)
pk = w.s([w.s([], 'simpll', '( %s -> %s )' % (P, P1))], 'simpld', '( %s -> ( %s /\\ k e. NN0 ) )' % (P, A3))
pa3 = w.s([pk], 'simpld', '( %s -> %s )' % (P, A3))
kn0 = w.s([pk], 'simprd', '( %s -> k e. NN0 )' % P)
h2 = w.s([w.s([], 'simpll', '( %s -> %s )' % (P, P1))], 'simprd', '( %s -> %s )' % (P, H2))
ln0 = w.s([], 'simplr', '( %s -> l e. NN0 )' % P)
h3 = w.s([], 'simpr', '( %s -> %s )' % (P, H3))
kre = w.s([kn0], 'nn0red', '( %s -> k e. RR )' % P)
lre = w.s([ln0], 'nn0red', '( %s -> l e. RR )' % P)
kz = w.s([kn0], 'nn0zd', '( %s -> k e. ZZ )' % P)
lz = w.s([ln0], 'nn0zd', '( %s -> l e. ZZ )' % P)
n3z = w.s([w.s([], '3z', '3 e. ZZ')], 'a1i', '( %s -> 3 e. ZZ )' % P)
n3re = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % P)
sum2 = w.s([kn0, ln0], 'nn0addcld', '( %s -> ( k + l ) e. NN0 )' % P)
kl0 = w.s([sum2, w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % P)], 'nn0addcld', '( %s -> %s e. NN0 )' % (P, KL))
klz = w.s([kl0], 'nn0zd', '( %s -> %s e. ZZ )' % (P, KL))
klre = w.s([kl0], 'nn0red', '( %s -> %s e. RR )' % (P, KL))
klre2 = w.s([sum2], 'nn0red', '( %s -> ( k + l ) e. RR )' % P)
le3 = w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], '3re', '3 e. RR'), w.s([], '3pos', '0 < 3')], 'ltleii', '0 <_ 3')], 'a1i', '( %s -> 0 <_ 3 )' % P)
kle1 = w.s([kre, lre], 'addge01d', '( %s -> ( 0 <_ l <-> k <_ ( k + l ) ) )' % P)
kle = w.s([w.s([ln0], 'nn0ge0d', '( %s -> 0 <_ l )' % P), kle1], 'mpbid', '( %s -> k <_ ( k + l ) )' % P)
klp = w.s([klre2, n3re], 'addge01d', '( %s -> ( 0 <_ 3 <-> ( k + l ) <_ %s ) )' % (P, KL))
klp2 = w.s([le3, klp], 'mpbid', '( %s -> ( k + l ) <_ %s )' % (P, KL))
kfin = w.s([kre, klre2, klre, kle, klp2], 'letrd', '( %s -> k <_ %s )' % (P, KL))
lle1 = w.s([lre, kre], 'addge02d', '( %s -> ( 0 <_ k <-> l <_ ( k + l ) ) )' % P)
lle = w.s([w.s([kn0], 'nn0ge0d', '( %s -> 0 <_ k )' % P), lle1], 'mpbid', '( %s -> l <_ ( k + l ) )' % P)
lfin = w.s([lre, klre2, klre, lle, klp2], 'letrd', '( %s -> l <_ %s )' % (P, KL))
tfin1 = w.s([n3re, klre2], 'addge02d', '( %s -> ( 0 <_ ( k + l ) <-> 3 <_ %s ) )' % (P, KL))
tfin = w.s([w.s([sum2], 'nn0ge0d', '( %s -> 0 <_ ( k + l ) )' % P), tfin1], 'mpbid', '( %s -> 3 <_ %s )' % (P, KL))
uk = w.s([w.s([kz, klz, kfin], '3jca', '( %s -> ( k e. ZZ /\\ %s e. ZZ /\\ k <_ %s ) )' % (P, KL, KL)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` k ) )' % (P, KL))
ul = w.s([w.s([lz, klz, lfin], '3jca', '( %s -> ( l e. ZZ /\\ %s e. ZZ /\\ l <_ %s ) )' % (P, KL, KL)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` l ) )' % (P, KL))
u3 = w.s([w.s([n3z, klz, tfin], '3jca', '( %s -> ( 3 e. ZZ /\\ %s e. ZZ /\\ 3 <_ %s ) )' % (P, KL, KL)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` 3 ) )' % (P, KL))
ssk = w.s([uk, w.inst('uzss')], 'syl', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` k ) )' % (P, KL))
ssl = w.s([ul, w.inst('uzss')], 'syl', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` l ) )' % (P, KL))
ss3 = w.s([u3, w.inst('uzss')], 'syl', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` 3 ) )' % (P, KL))
nel = w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` %s ) )' % (Q, KL))
nk = w.s([w.s([ssk], 'adantr', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` k ) )' % (Q, KL)), nel], 'sseldd', '( %s -> n e. ( ZZ>= ` k ) )' % Q)
nl = w.s([w.s([ssl], 'adantr', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` l ) )' % (Q, KL)), nel], 'sseldd', '( %s -> n e. ( ZZ>= ` l ) )' % Q)
n3 = w.s([w.s([ss3], 'adantr', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` 3 ) )' % (Q, KL)), nel], 'sseldd', '( %s -> n e. ( ZZ>= ` 3 ) )' % Q)
r2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % Q)
e2r = w.s([r2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (Q, E2('n')))
e3r = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (Q, E3('n')))
h2q = w.s([h2], 'adantr', '( %s -> %s )' % (Q, H2))
h3q = w.s([h3], 'adantr', '( %s -> %s )' % (Q, H3))
fi2 = w.s([], 'fveq2', '( i = n -> ( ell2 ` i ) = ( ell2 ` n ) )')
cg2 = w.s([fi2], 'breq2d', '( i = n -> ( %s <-> %s ) )' % (B2('i'), B2('n')))
g2 = w.s([cg2, h2q, nk], 'rspcdva', '( %s -> %s )' % (Q, B2('n')))
fj3 = w.s([], 'fveq2', '( j = n -> ( ell3 ` j ) = ( ell3 ` n ) )')
cg3 = w.s([fj3], 'breq2d', '( j = n -> ( %s <-> %s ) )' % (B3('j'), B3('n')))
g3 = w.s([cg3, h3q, nl], 'rspcdva', '( %s -> %s )' % (Q, B3('n')))
aq = w.s([pa3], 'adantr', '( %s -> %s )' % (Q, A3))
crq, c0q, brq = a3parts(Q, aq)
crpq, bcq, abq, geq, g0q = abcsteps(Q, crq, c0q, brq)
bce = w.s([bcq, abq, e2r, geq, g2], 'letrd', '( %s -> ( B / C ) <_ %s )' % (Q, E2('n')))
e20 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Q), abq, e2r, g0q, g2], 'letrd', '( %s -> 0 <_ %s )' % (Q, E2('n')))
bi = w.s([brq, e2r, crpq], 'ledivmuld', '( %s -> ( ( B / C ) <_ %s <-> B <_ ( C x. %s ) ) )' % (Q, E2('n'), E2('n')))
bmul = w.s([bce, bi], 'mpbid', '( %s -> B <_ ( C x. %s ) )' % (Q, E2('n')))
cl2 = w.s([crq, e2r], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (Q, E2('n')))
cl20 = w.s([crq, e2r, w.s([crq, c0q], 'ltled', '( %s -> 0 <_ C )' % Q), e20], 'mulge0d', '( %s -> 0 <_ ( C x. %s ) )' % (Q, E2('n')))
zrr = w.s([cl2, e3r], 'remulcld', '( %s -> %s e. RR )' % (Q, ZR('n')))
mge = w.s([cl2, e3r, cl20, g3], 'lemulge11d', '( %s -> ( C x. %s ) <_ %s )' % (Q, E2('n'), ZR('n')))
fin = w.s([brq, cl2, zrr, bmul, mge], 'letrd', '( %s -> B <_ %s )' % (Q, ZR('n')))
ralf = w.s([fin], 'ralrimiva', '( %s -> A. n e. ( ZZ>= ` %s ) B <_ %s )' % (P, KL, ZR('n')))
P5 = '( %s /\\ m = %s )' % (P, KL)
idm = w.s([], 'simpr', '( %s -> m = %s )' % (P5, KL))
cgm, bm = w.wcongr('A. n e. ( ZZ>= ` m ) B <_ %s' % ZR('n'), {'m': KL}, P5, {'m': idm})
assert bm == 'A. n e. ( ZZ>= ` %s ) B <_ %s' % (KL, ZR('n')), bm
exg = w.s([kl0, cgm, ralf], 'rspcedvd', '( %s -> %s )' % (P, GOAL))
exl = w.s([exg], 'ex', '( ( %s /\\ l e. NN0 ) -> ( %s -> %s ) )' % (P1, H3, GOAL))
rll = w.s([exl], 'rexlimdva', '( %s -> ( E. l e. NN0 %s -> %s ) )' % (P1, H3, GOAL))
a3p1 = w.s([], 'simpll', '( %s -> %s )' % (P1, A3))
ex3p1 = w.s([a3p1, ex3], 'syl', '( %s -> E. l e. NN0 %s )' % (P1, H3))
gl = w.s([ex3p1, rll], 'mpd', '( %s -> %s )' % (P1, GOAL))
exk = w.s([gl], 'ex', '( ( %s /\\ k e. NN0 ) -> ( %s -> %s ) )' % (A3, H2, GOAL))
rlk = w.s([exk], 'rexlimdva', '( %s -> ( E. k e. NN0 %s -> %s ) )' % (A3, H2, GOAL))
w.qed([ex2, rlk], 'mpd', '( %s -> %s )' % (A3, GOAL))
run(w)
