"""C5, character block: the translated block sum of a nonprincipal character,
the periodicity of its partial sums, and the partial-sum bound
norm_charSum_le, packaged as C4's bounded-partial-sum interface."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

WIF = '( 0 ..^ N )'
WI = 'if ( N = 0 , ZZ , %s )' % WIF


def chrctx(w, A1, chr_=None):
    """the standing steps of CHR under A1"""
    d = {}
    if chr_ is None:
        chr_ = w.s([], 'id', '( %s -> %s )' % (A1, CHR))
    d['chr'] = chr_
    nx = w.s([chr_, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A1, DC))
    d['nx'] = nx
    d['nn'] = w.s([nx, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A1)
    d['xd'] = w.s([nx, w.inst('simpr')], 'syl', '( %s -> X e. %s )' % (A1, DC))
    d['xne'] = w.s([chr_, w.inst('simpr')], 'syl', '( %s -> X =/= %s )' % (A1, ONE))
    d['g'], d['z'], d['b'], d['l'] = dchyp(w)
    d['bb'] = w.s([], 'eqid', '%s = %s' % (BZ, BZ))
    d['nn0'] = w.s([d['nn']], 'nnnn0d', '( %s -> N e. NN0 )' % A1)
    d['nz'] = w.s([d['nn']], 'nnzd', '( %s -> N e. ZZ )' % A1)
    return d


def chvcl(w, ante, K, nx, mk):
    """( ante -> CHV(K) e. CC ) from nx: ( N e. NN /\\ X e. DC ), mk: K e. NN"""
    return w.s([w.s([nx, mk], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ %s e. NN ) )' % (ante, DC, K)), w.inst('lchrcl')], 'syl',
               '( %s -> %s e. CC )' % (ante, CHV(K)))


# ---------------------------------------------------------------- chrtrl
w = W('chrtrl', 'The ring homomorphism from the integers to ` Z/nZ ` is additive ( ~ zrhrhm , ~ ghmlin ).')
A0 = '( N e. NN /\\ J e. ZZ /\\ K e. ZZ )'
nn = w.s([], 'simp1', '( %s -> N e. NN )' % A0)
jz = w.s([], 'simp2', '( %s -> J e. ZZ )' % A0)
kz = w.s([], 'simp3', '( %s -> K e. ZZ )' % A0)
z = w.s([], 'eqid', '%s = %s' % (ZN, ZN)); l = w.s([], 'eqid', '%s = %s' % (LH, LH))
rng = w.s([w.s([w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0), w.s([z], 'zncrng', '( N e. NN0 -> %s e. CRing )' % ZN)], 'syl',
               '( %s -> %s e. CRing )' % (A0, ZN)), w.inst('crngring')], 'syl', '( %s -> %s e. Ring )' % (A0, ZN))
rhm = w.s([rng, w.s([l], 'zrhrhm', '( %s e. Ring -> %s e. ( ZZring RingHom %s ) )' % (ZN, LH, ZN))], 'syl',
          '( %s -> %s e. ( ZZring RingHom %s ) )' % (A0, LH, ZN))
ghm = w.s([rhm, w.inst('rhmghm')], 'syl', '( %s -> %s e. ( ZZring GrpHom %s ) )' % (A0, LH, ZN))
zb = w.s([], 'zringbas', 'ZZ = ( Base ` ZZring )')
zp = w.s([], 'zringplusg', '+ = ( +g ` ZZring )')
pg = w.s([], 'eqid', '%s = %s' % (PG, PG))
lin = w.s([zb, zp, pg], 'ghmlin', '( ( %s e. ( ZZring GrpHom %s ) /\\ J e. ZZ /\\ K e. ZZ ) -> ( %s ` ( J + K ) ) = ( ( %s ` J ) %s ( %s ` K ) ) )' % (LH, ZN, LH, LH, PG, LH))
w.qed([ghm, jz, kz, lin], 'syl3anc', '( %s -> ( %s ` ( J + K ) ) = ( ( %s ` J ) %s ( %s ` K ) ) )' % (A0, LH, LH, PG, LH))
run5(w)

# ---------------------------------------------------------------- chrblk
w = W('chrblk', 'A nonprincipal Dirichlet character sums to zero over any block of ` N ` consecutive '
      'positive integers: the translated form of ~ dchrper .')
A0 = '( %s /\\ J e. NN0 )' % CHR
d = chrctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, CHR)))
jn0 = w.s([], 'simpr', '( %s -> J e. NN0 )' % A0)
K = '( J + 1 )'
kn = w.s([jn0, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A0, K))
kz = w.s([kn], 'nnzd', '( %s -> %s e. ZZ )' % (A0, K))
kc = w.s([kn], 'nncnd', '( %s -> %s e. CC )' % (A0, K))
nc = w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % A0)
one = a1(w, A0, 'ax-1cn', '1 e. CC')
nm1 = w.s([d['nz'], a1(w, A0, '1z', '1 e. ZZ')], 'zsubcld', '( %s -> ( N - 1 ) e. ZZ )' % A0)
z0 = a1(w, A0, '0z', '0 e. ZZ')
# 1. the index set ( ( J + 1 ) ... ( J + N ) ) = ( ( 0 + K ) ... ( ( N - 1 ) + K ) )
e1 = w.s([kc], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A0, K, K))
e2 = w.s([w.s([w.s([nc, one], 'subcld', '( %s -> ( N - 1 ) e. CC )' % A0), kc], 'addcomd', '( %s -> ( ( N - 1 ) + %s ) = ( %s + ( N - 1 ) ) )' % (A0, K, K)),
          w.s([w.s([w.s([jn0], 'nn0cnd', '( %s -> J e. CC )' % A0), one, w.s([nc, one], 'subcld', '( %s -> ( N - 1 ) e. CC )' % A0)], 'addassd',
                   '( %s -> ( ( J + 1 ) + ( N - 1 ) ) = ( J + ( 1 + ( N - 1 ) ) ) )' % A0),
               w.s([w.s([one, nc], 'pncan3d', '( %s -> ( 1 + ( N - 1 ) ) = N )' % A0)], 'oveq2d', '( %s -> ( J + ( 1 + ( N - 1 ) ) ) = ( J + N ) )' % A0)],
              'eqtrd', '( %s -> ( ( J + 1 ) + ( N - 1 ) ) = ( J + N ) )' % A0)], 'eqtrd', '( %s -> ( ( N - 1 ) + %s ) = ( J + N ) )' % (A0, K))
iset = w.s([w.s([e1, e2], 'oveq12d', '( %s -> ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) = ( %s ... ( J + N ) ) )' % (A0, K, K, K))], 'eqcomd',
           '( %s -> ( %s ... ( J + N ) ) = ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) )' % (A0, K, K, K))
s1 = w.s([iset], 'sumeq1d', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (A0, K, CHV('i'), K, K, CHV('i')))
# 2. the body as CHV( K + ( i - K ) )
Ai = '( %s /\\ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) )' % (A0, K, K)
ic = w.s([w.s([w.s([], 'simpr', '( %s -> i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) )' % (Ai, K, K)), w.inst('elfzelz')], 'syl', '( %s -> i e. ZZ )' % Ai)], 'zcnd',
         '( %s -> i e. CC )' % Ai)
pc = w.s([w.s([kc], 'adantr', '( %s -> %s e. CC )' % (Ai, K)), ic], 'pncan3d', '( %s -> ( %s + ( i - %s ) ) = i )' % (Ai, K, K))
s2 = w.s([w.s([w.s([w.s([pc], 'fveq2d', '( %s -> ( %s ` ( %s + ( i - %s ) ) ) = ( %s ` i ) )' % (Ai, LH, K, K, LH))], 'fveq2d',
                    '( %s -> %s = %s )' % (Ai, CHV('( %s + ( i - %s ) )' % (K, K)), CHV('i')))], 'eqcomd', '( %s -> %s = %s )' % (Ai, CHV('i'), CHV('( %s + ( i - %s ) )' % (K, K))))],
         'sumeq2dv', '( %s -> sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (A0, K, K, CHV('i'), K, K, CHV('( %s + ( i - %s ) )' % (K, K))))
# 3. fsumshft back to ( 0 ... ( N - 1 ) )
Aj = '( %s /\\ j e. ( 0 ... ( N - 1 ) ) )' % A0
jn0 = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... ( N - 1 ) ) )' % Aj), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % Aj)
kjn = w.s([w.s([kn], 'adantr', '( %s -> %s e. NN )' % (Aj, K)), jn0, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( %s + j ) e. NN )' % (Aj, K))
acl = chvcl(w, Aj, '( %s + j )' % K, w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Aj, DC)), kjn)
sub = w.s([w.s([w.s([], 'oveq2', '( j = ( i - %s ) -> ( %s + j ) = ( %s + ( i - %s ) ) )' % (K, K, K, K))], 'fveq2d',
               '( j = ( i - %s ) -> ( %s ` ( %s + j ) ) = ( %s ` ( %s + ( i - %s ) ) ) )' % (K, LH, K, LH, K, K))], 'fveq2d',
          '( j = ( i - %s ) -> %s = %s )' % (K, CHV('( %s + j )' % K), CHV('( %s + ( i - %s ) )' % (K, K))))
sh = w.s([kz, z0, nm1, acl, sub], 'fsumshft', '( %s -> sum_ j e. ( 0 ... ( N - 1 ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (
    A0, CHV('( %s + j )' % K), K, K, CHV('( %s + ( i - %s ) )' % (K, K))))
# 4. ( 0 ... ( N - 1 ) ) = W and the body by chrtrl
fzo = w.s([w.s([d['nz'], w.inst('fzoval')], 'syl', '( %s -> %s = ( 0 ... ( N - 1 ) ) )' % (A0, WIF))], 'eqcomd', '( %s -> ( 0 ... ( N - 1 ) ) = %s )' % (A0, WIF))
weq = w.s([w.s([w.s([d['nn']], 'nnne0d', '( %s -> N =/= 0 )' % A0), w.inst('ifnefalse')], 'syl', '( %s -> %s = %s )' % (A0, WI, WIF))], 'eqcomd',
          '( %s -> %s = %s )' % (A0, WIF, WI))
iw = w.s([fzo, weq], 'eqtrd', '( %s -> ( 0 ... ( N - 1 ) ) = %s )' % (A0, WI))
s4 = w.s([iw], 'sumeq1d', '( %s -> sum_ j e. ( 0 ... ( N - 1 ) ) %s = sum_ j e. %s %s )' % (A0, CHV('( %s + j )' % K), WI, CHV('( %s + j )' % K)))
Aw = '( %s /\\ j e. %s )' % (A0, WI)
jw = w.s([], 'simpr', '( %s -> j e. %s )' % (Aw, WI))
jwf = w.s([jw, w.s([weq], 'adantr', '( %s -> %s = %s )' % (Aw, WIF, WI))], 'eleqtrrd', '( %s -> j e. %s )' % (Aw, WIF))
jz = w.s([jwf, w.inst('elfzoelz')], 'syl', '( %s -> j e. ZZ )' % Aw)
C = '( %s ` %s )' % (LH, K)
trl = w.s([w.s([w.s([d['nn']], 'adantr', '( %s -> N e. NN )' % Aw), w.s([kz], 'adantr', '( %s -> %s e. ZZ )' % (Aw, K)), jz], '3jca',
                '( %s -> ( N e. NN /\\ %s e. ZZ /\\ j e. ZZ ) )' % (Aw, K)), w.inst('chrtrl')], 'syl',
          '( %s -> ( %s ` ( %s + j ) ) = ( %s %s ( %s ` j ) ) )' % (Aw, LH, K, C, PG, LH))
s5 = w.s([w.s([trl], 'fveq2d', '( %s -> %s = ( X ` ( %s %s ( %s ` j ) ) ) )' % (Aw, CHV('( %s + j )' % K), C, PG, LH))], 'sumeq2dv',
         '( %s -> sum_ j e. %s %s = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, WI, CHV('( %s + j )' % K), WI, C, PG, LH))
# 5. reindex onto the base along znf1o
fr = w.s([], 'eqid', '( %s |` %s ) = ( %s |` %s )' % (LH, WI, LH, WI))
wq = w.s([], 'eqid', '%s = %s' % (WI, WI))
f1o = w.s([d['nn0'], w.s([d['z'], d['bb'], fr, wq], 'znf1o', '( N e. NN0 -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (LH, WI, WI, BZ))], 'syl',
          '( %s -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (A0, LH, WI, WI, BZ))
wfin = w.s([w.s([weq], 'eqcomd', '( %s -> %s = %s )' % (A0, WI, WIF)), a1(w, A0, 'fzofi', '%s e. Fin' % WIF)], 'eqeltrd', '( %s -> %s e. Fin )' % (A0, WI))
fres = w.s([jw, w.inst('fvres')], 'syl', '( %s -> ( ( %s |` %s ) ` j ) = ( %s ` j ) )' % (Aw, LH, WI, LH))
xf = w.s([d['g'], d['z'], d['b'], d['bb'], d['xd']], 'dchrf', '( %s -> X : %s --> CC )' % (A0, BZ))
grp = w.s([w.s([w.s([d['nn0'], w.s([d['z']], 'zncrng', '( N e. NN0 -> %s e. CRing )' % ZN)], 'syl', '( %s -> %s e. CRing )' % (A0, ZN)),
                w.inst('crngring')], 'syl', '( %s -> %s e. Ring )' % (A0, ZN)), w.inst('ringgrp')], 'syl', '( %s -> %s e. Grp )' % (A0, ZN))
lf = w.s([w.s([d['nn0'], w.s([d['z'], d['bb'], d['l']], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> %s )' % (LH, BZ))], 'syl',
              '( %s -> %s : ZZ -onto-> %s )' % (A0, LH, BZ)), w.inst('fof')], 'syl', '( %s -> %s : ZZ --> %s )' % (A0, LH, BZ))
cb = w.s([lf, kz], 'ffvelcdmd', '( %s -> %s e. %s )' % (A0, C, BZ))
Aa = '( %s /\\ a e. %s )' % (A0, BZ)
ab = w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, BZ))
cab = w.s([w.s([grp], 'adantr', '( %s -> %s e. Grp )' % (Aa, ZN)), w.s([cb], 'adantr', '( %s -> %s e. %s )' % (Aa, C, BZ)), ab,
           w.s([d['bb'], w.s([], 'eqid', '%s = %s' % (PG, PG))], 'grpcl', '( ( %s e. Grp /\\ %s e. %s /\\ a e. %s ) -> ( %s %s a ) e. %s )' % (ZN, C, BZ, BZ, C, PG, BZ))],
          'syl3anc', '( %s -> ( %s %s a ) e. %s )' % (Aa, C, PG, BZ))
xcab = w.s([w.s([xf], 'adantr', '( %s -> X : %s --> CC )' % (Aa, BZ)), cab], 'ffvelcdmd', '( %s -> ( X ` ( %s %s a ) ) e. CC )' % (Aa, C, PG))
sub5 = w.s([w.s([], 'oveq2', '( a = ( %s ` j ) -> ( %s %s a ) = ( %s %s ( %s ` j ) ) )' % (LH, C, PG, C, PG, LH))], 'fveq2d',
           '( a = ( %s ` j ) -> ( X ` ( %s %s a ) ) = ( X ` ( %s %s ( %s ` j ) ) ) )' % (LH, C, PG, C, PG, LH))
s6 = w.s([sub5, wfin, f1o, fres, xcab], 'fsumf1o', '( %s -> sum_ a e. %s ( X ` ( %s %s a ) ) = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, BZ, C, PG, WI, C, PG, LH))
# 6. the translation of the base
TF = '( t e. %s |-> ( %s %s t ) )' % (BZ, C, PG)
tf1o = w.s([grp, cb, w.s([d['bb'], w.s([], 'eqid', '%s = %s' % (PG, PG)), w.s([], 'eqid', '%s = %s' % (TF, TF))], 'grplmulf1o',
                          '( ( %s e. Grp /\\ %s e. %s ) -> %s : %s -1-1-onto-> %s )' % (ZN, C, BZ, TF, BZ, BZ))], 'syl2anc',
           '( %s -> %s : %s -1-1-onto-> %s )' % (A0, TF, BZ, BZ))
bfin = w.s([d['nn'], w.s([d['z'], d['bb']], 'znfi', '( N e. NN -> %s e. Fin )' % BZ)], 'syl', '( %s -> %s e. Fin )' % (A0, BZ))
tsub = w.s([], 'oveq2', '( t = a -> ( %s %s t ) = ( %s %s a ) )' % (C, PG, C, PG))
tfv = mpv(w, Aa, TF, 'a', '( %s %s a )' % (C, PG), tsub, ab, vexd(w, Aa, '( %s %s a )' % (C, PG)), BZ)
Ab = '( %s /\\ b e. %s )' % (A0, BZ)
xb = w.s([w.s([xf], 'adantr', '( %s -> X : %s --> CC )' % (Ab, BZ)), w.s([], 'simpr', '( %s -> b e. %s )' % (Ab, BZ))], 'ffvelcdmd', '( %s -> ( X ` b ) e. CC )' % Ab)
sub6 = w.s([], 'fveq2', '( b = ( %s %s a ) -> ( X ` b ) = ( X ` ( %s %s a ) ) )' % (C, PG, C, PG))
s7 = w.s([sub6, bfin, tf1o, tfv, xb], 'fsumf1o', '( %s -> sum_ b e. %s ( X ` b ) = sum_ a e. %s ( X ` ( %s %s a ) ) )' % (A0, BZ, BZ, C, PG))
# 7. dchrsum
o1 = w.s([], 'eqid', '%s = %s' % (ONE, ONE))
dsum = w.s([d['g'], d['z'], d['b'], o1, d['xd'], d['bb']], 'dchrsum', '( %s -> sum_ b e. %s ( X ` b ) = if ( X = %s , ( phi ` N ) , 0 ) )' % (A0, BZ, ONE))
base0 = w.s([dsum, w.s([d['xne'], w.inst('ifnefalse')], 'syl', '( %s -> if ( X = %s , ( phi ` N ) , 0 ) = 0 )' % (A0, ONE))], 'eqtrd',
            '( %s -> sum_ b e. %s ( X ` b ) = 0 )' % (A0, BZ))
# assemble
c1 = w.s([s1, s2], 'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s )' % (A0, K, CHV('i'), K, K, CHV('( %s + ( i - %s ) )' % (K, K))))
c2 = w.s([c1, w.s([sh], 'eqcomd', '( %s -> sum_ i e. ( ( 0 + %s ) ... ( ( N - 1 ) + %s ) ) %s = sum_ j e. ( 0 ... ( N - 1 ) ) %s )' % (A0, K, K, CHV('( %s + ( i - %s ) )' % (K, K)), CHV('( %s + j )' % K)))],
         'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ j e. ( 0 ... ( N - 1 ) ) %s )' % (A0, K, CHV('i'), CHV('( %s + j )' % K)))
c3 = w.s([c2, w.s([s4, s5], 'eqtrd', '( %s -> sum_ j e. ( 0 ... ( N - 1 ) ) %s = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, CHV('( %s + j )' % K), WI, C, PG, LH))],
         'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) )' % (A0, K, CHV('i'), WI, C, PG, LH))
c4 = w.s([c3, w.s([s6], 'eqcomd', '( %s -> sum_ j e. %s ( X ` ( %s %s ( %s ` j ) ) ) = sum_ a e. %s ( X ` ( %s %s a ) ) )' % (A0, WI, C, PG, LH, BZ, C, PG))], 'eqtrd',
         '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ a e. %s ( X ` ( %s %s a ) ) )' % (A0, K, CHV('i'), BZ, C, PG))
c5 = w.s([c4, w.s([s7], 'eqcomd', '( %s -> sum_ a e. %s ( X ` ( %s %s a ) ) = sum_ b e. %s ( X ` b ) )' % (A0, BZ, C, PG, BZ))], 'eqtrd',
         '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = sum_ b e. %s ( X ` b ) )' % (A0, K, CHV('i'), BZ))
w.qed([c5, base0], 'eqtrd', '( %s -> sum_ i e. ( %s ... ( J + N ) ) %s = 0 )' % (A0, K, CHV('i')))
run5(w)

# ---------------------------------------------------------------- chrsper
w = W('chrsper', 'The partial sums of a nonprincipal Dirichlet character are periodic with period ` N ` '
      '( Lean ` charSum_add_period ` ).')
A0 = '( %s /\\ J e. NN0 )' % CHR
d = chrctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, CHR)))
jn0 = w.s([], 'simpr', '( %s -> J e. NN0 )' % A0)
jr = w.s([jn0], 'nn0red', '( %s -> J e. RR )' % A0)
jz = w.s([jn0], 'nn0zd', '( %s -> J e. ZZ )' % A0)
A_ = '( 1 ... J )'; B_ = '( ( J + 1 ) ... ( J + N ) )'; U_ = '( 1 ... ( J + N ) )'
dis = w.s([w.s([jr], 'ltp1d', '( %s -> J < ( J + 1 ) )' % A0), w.inst('fzdisj')], 'syl', '( %s -> ( %s i^i %s ) = (/) )' % (A0, A_, B_))
j1u = w.s([w.s([jn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( J + 1 ) e. NN )' % A0), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> ( J + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
jnz = w.s([jz, d['nz']], 'zaddcld', '( %s -> ( J + N ) e. ZZ )' % A0)
jle = w.s([jr, d['nn0'], w.inst('nn0addge1')], 'syl2anc', '( %s -> J <_ ( J + N ) )' % A0)
jnu = w.s([w.s([jz, jnz, jle], '3jca', '( %s -> ( J e. ZZ /\\ ( J + N ) e. ZZ /\\ J <_ ( J + N ) ) )' % A0),
           w.s([], 'eluz2', '( ( J + N ) e. ( ZZ>= ` J ) <-> ( J e. ZZ /\\ ( J + N ) e. ZZ /\\ J <_ ( J + N ) ) )')], 'sylibr', '( %s -> ( J + N ) e. ( ZZ>= ` J ) )' % A0)
spl = w.s([j1u, jnu, w.inst('fzsplit2')], 'syl2anc', '( %s -> %s = ( %s u. %s ) )' % (A0, U_, A_, B_))
fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, U_))
Ai = '( %s /\\ i e. %s )' % (A0, U_)
icl = chvcl(w, Ai, 'i', w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ai, DC)),
            w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, U_)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai))
sp = w.s([dis, spl, fin, icl], 'fsumsplit', '( %s -> %s = ( %s + sum_ i e. %s %s ) )' % (A0, CSUM('( J + N )'), CSUM('J'), B_, CHV('i')))
blk = w.s([], 'chrblk', '( %s -> sum_ i e. %s %s = 0 )' % (A0, B_, CHV('i')))
Aj = '( %s /\\ i e. %s )' % (A0, A_)
jcl = chvcl(w, Aj, 'i', w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Aj, DC)),
            w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Aj, A_)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Aj))
scl = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, A_)), jcl], 'fsumcl', '( %s -> %s e. CC )' % (A0, CSUM('J')))
w.qed([sp, w.s([w.s([blk], 'oveq2d', '( %s -> ( %s + sum_ i e. %s %s ) = ( %s + 0 ) )' % (A0, CSUM('J'), B_, CHV('i'), CSUM('J'))),
                w.s([scl], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A0, CSUM('J'), CSUM('J')))], 'eqtrd',
               '( %s -> ( %s + sum_ i e. %s %s ) = %s )' % (A0, CSUM('J'), B_, CHV('i'), CSUM('J')))], 'eqtrd',
      '( %s -> %s = %s )' % (A0, CSUM('( J + N )'), CSUM('J')))
run5(w)

# ---------------------------------------------------------------- chrsmod
w = W('chrsmod', 'The partial sums of a nonprincipal Dirichlet character depend only on the index modulo ` N ` '
      '( ~ nn0ind on the number of periods; Lean ` charSum_mod ` ).')
C0 = '( %s /\\ P e. NN0 )' % CHR
S0 = CSUM('P')


def PH(x):
    return '( %s -> %s = %s )' % (C0, CSUM('( P + ( N x. %s ) )' % x), S0)


def SUBH(x, t):
    """( x = t -> ( PH(x) <-> PH(t) ) )"""
    s = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( N x. %s ) = ( N x. %s ) )' % (x, t, x, t))], 'oveq2d',
                       '( %s = %s -> ( P + ( N x. %s ) ) = ( P + ( N x. %s ) ) )' % (x, t, x, t))], 'oveq2d',
                  '( %s = %s -> ( 1 ... ( P + ( N x. %s ) ) ) = ( 1 ... ( P + ( N x. %s ) ) ) )' % (x, t, x, t))], 'sumeq1d',
             '( %s = %s -> %s = %s )' % (x, t, CSUM('( P + ( N x. %s ) )' % x), CSUM('( P + ( N x. %s ) )' % t)))
    e = w.s([s], 'eqeq1d', '( %s = %s -> ( %s = %s <-> %s = %s ) )' % (x, t, CSUM('( P + ( N x. %s ) )' % x), S0, CSUM('( P + ( N x. %s ) )' % t), S0))
    return w.s([e], 'imbi2d', '( %s = %s -> ( %s <-> %s ) )' % (x, t, PH(x), PH(t)))


h1 = SUBH('x', '0'); h2 = SUBH('x', 'y'); h3 = SUBH('x', '( y + 1 )'); h4 = SUBH('x', 'Q')
# base
d = chrctx(w, C0, w.s([], 'simpl', '( %s -> %s )' % (C0, CHR)))
pn0 = w.s([], 'simpr', '( %s -> P e. NN0 )' % C0)
pc = w.s([pn0], 'nn0cnd', '( %s -> P e. CC )' % C0)
nc = w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % C0)
b1 = w.s([w.s([w.s([nc], 'mul01d', '( %s -> ( N x. 0 ) = 0 )' % C0)], 'oveq2d', '( %s -> ( P + ( N x. 0 ) ) = ( P + 0 ) )' % C0),
          w.s([pc], 'addridd', '( %s -> ( P + 0 ) = P )' % C0)], 'eqtrd', '( %s -> ( P + ( N x. 0 ) ) = P )' % C0)
base = w.s([w.s([b1], 'oveq2d', '( %s -> ( 1 ... ( P + ( N x. 0 ) ) ) = ( 1 ... P ) )' % C0)], 'sumeq1d', PH('0'))
# step
Ay = '( y e. NN0 /\\ %s )' % C0
yn0 = w.s([], 'simpl', '( %s -> y e. NN0 )' % Ay)
c0 = w.s([], 'simpr', '( %s -> %s )' % (Ay, C0))
dy = chrctx(w, Ay, w.s([c0, w.inst('simpl')], 'syl', '( %s -> %s )' % (Ay, CHR)))
pn0y = w.s([c0, w.inst('simpr')], 'syl', '( %s -> P e. NN0 )' % Ay)
ncy = w.s([dy['nn']], 'nncnd', '( %s -> N e. CC )' % Ay)
yc = w.s([yn0], 'nn0cnd', '( %s -> y e. CC )' % Ay)
pcy = w.s([pn0y], 'nn0cnd', '( %s -> P e. CC )' % Ay)
J_ = '( P + ( N x. y ) )'
e1 = w.s([w.s([ncy, yc, a1(w, Ay, 'ax-1cn', '1 e. CC')], 'adddid', '( %s -> ( N x. ( y + 1 ) ) = ( ( N x. y ) + ( N x. 1 ) ) )' % Ay),
          w.s([w.s([ncy], 'mulridd', '( %s -> ( N x. 1 ) = N )' % Ay)], 'oveq2d', '( %s -> ( ( N x. y ) + ( N x. 1 ) ) = ( ( N x. y ) + N ) )' % Ay)], 'eqtrd',
         '( %s -> ( N x. ( y + 1 ) ) = ( ( N x. y ) + N ) )' % Ay)
e2 = w.s([w.s([e1], 'oveq2d', '( %s -> ( P + ( N x. ( y + 1 ) ) ) = ( P + ( ( N x. y ) + N ) ) )' % Ay),
          w.s([w.s([pcy, w.s([ncy, yc], 'mulcld', '( %s -> ( N x. y ) e. CC )' % Ay), ncy], 'addassd', '( %s -> ( ( P + ( N x. y ) ) + N ) = ( P + ( ( N x. y ) + N ) ) )' % Ay)],
              'eqcomd', '( %s -> ( P + ( ( N x. y ) + N ) ) = ( %s + N ) )' % (Ay, J_))], 'eqtrd', '( %s -> ( P + ( N x. ( y + 1 ) ) ) = ( %s + N ) )' % (Ay, J_))
s1 = w.s([w.s([e2], 'oveq2d', '( %s -> ( 1 ... ( P + ( N x. ( y + 1 ) ) ) ) = ( 1 ... ( %s + N ) ) )' % (Ay, J_))], 'sumeq1d',
         '( %s -> %s = %s )' % (Ay, CSUM('( P + ( N x. ( y + 1 ) ) )'), CSUM('( %s + N )' % J_)))
jn0 = w.s([pn0y, w.s([dy['nn0'], yn0], 'nn0mulcld', '( %s -> ( N x. y ) e. NN0 )' % Ay)], 'nn0addcld', '( %s -> %s e. NN0 )' % (Ay, J_))
per = w.s([w.s([dy['chr'], jn0], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (Ay, CHR, J_)), w.inst('chrsper')], 'syl',
          '( %s -> %s = %s )' % (Ay, CSUM('( %s + N )' % J_), CSUM(J_)))
s12 = w.s([s1, per], 'eqtrd', '( %s -> %s = %s )' % (Ay, CSUM('( P + ( N x. ( y + 1 ) ) )'), CSUM(J_)))
Ayh = '( %s /\\ %s = %s )' % (Ay, CSUM(J_), S0)
st = w.s([w.s([s12], 'adantr', '( %s -> %s = %s )' % (Ayh, CSUM('( P + ( N x. ( y + 1 ) ) )'), CSUM(J_))),
          w.s([], 'simpr', '( %s -> %s = %s )' % (Ayh, CSUM(J_), S0))], 'eqtrd', '( %s -> %s = %s )' % (Ayh, CSUM('( P + ( N x. ( y + 1 ) ) )'), S0))
st1 = w.s([st], 'ex', '( %s -> ( %s = %s -> %s = %s ) )' % (Ay, CSUM(J_), S0, CSUM('( P + ( N x. ( y + 1 ) ) )'), S0))
st2 = w.s([st1], 'ex', '( y e. NN0 -> ( %s -> ( %s = %s -> %s = %s ) ) )' % (C0, CSUM(J_), S0, CSUM('( P + ( N x. ( y + 1 ) ) )'), S0))
step = w.s([st2], 'a2d', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH('( y + 1 )')))
ind = w.s([h1, h2, h3, h4, base, step], 'nn0ind', '( Q e. NN0 -> %s )' % PH('Q'))
w.qed([w.s([w.s([ind], 'com12', '( %s -> ( Q e. NN0 -> %s = %s ) )' % (C0, CSUM('( P + ( N x. Q ) )'), S0))], 'imp',
           '( ( %s /\\ Q e. NN0 ) -> %s = %s )' % (C0, CSUM('( P + ( N x. Q ) )'), S0))], 'anasss',
      '( ( %s /\\ ( P e. NN0 /\\ Q e. NN0 ) ) -> %s = %s )' % (CHR, CSUM('( P + ( N x. Q ) )'), S0))
run5(w)

# ---------------------------------------------------------------- chrsbnd
w = W('chrsbnd', 'The partial sums of a nonprincipal Dirichlet character are bounded by the modulus: '
      'Lean\'s ` norm_charSum_le ` of LGrowth.lean.')
A0 = '( %s /\\ M e. NN0 )' % CHR
d = chrctx(w, A0, w.s([], 'simpl', '( %s -> %s )' % (A0, CHR)))
mn0 = w.s([], 'simpr', '( %s -> M e. NN0 )' % A0)
mr = w.s([mn0], 'nn0red', '( %s -> M e. RR )' % A0)
mz = w.s([mn0], 'nn0zd', '( %s -> M e. ZZ )' % A0)
nrp = w.s([d['nn']], 'nnrpd', '( %s -> N e. RR+ )' % A0)
nr = w.s([d['nn']], 'nnred', '( %s -> N e. RR )' % A0)
R_ = '( M mod N )'; Q_ = '( |_ ` ( M / N ) )'
mv = w.s([mr, nrp, w.inst('modval')], 'syl2anc', '( %s -> %s = ( M - ( N x. %s ) ) )' % (A0, R_, Q_))
rn0 = w.s([mz, d['nn'], w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, R_))
mdn = w.s([mr, nrp], 'rerpdivcld', '( %s -> ( M / N ) e. RR )' % A0)
mdg = w.s([w.s([mr, w.s([mn0], 'nn0ge0d', '( %s -> 0 <_ M )' % A0)], 'jca', '( %s -> ( M e. RR /\\ 0 <_ M ) )' % A0),
           w.s([nr, w.s([d['nn']], 'nngt0d', '( %s -> 0 < N )' % A0)], 'jca', '( %s -> ( N e. RR /\\ 0 < N ) )' % A0), w.inst('divge0')], 'syl2anc',
          '( %s -> 0 <_ ( M / N ) )' % A0)
qn0 = w.s([mdn, mdg, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, Q_))
nq = w.s([w.s([d['nn']], 'nncnd', '( %s -> N e. CC )' % A0), w.s([qn0], 'nn0cnd', '( %s -> %s e. CC )' % (A0, Q_))], 'mulcld', '( %s -> ( N x. %s ) e. CC )' % (A0, Q_))
idm = w.s([w.s([mv], 'oveq1d', '( %s -> ( %s + ( N x. %s ) ) = ( ( M - ( N x. %s ) ) + ( N x. %s ) ) )' % (A0, R_, Q_, Q_, Q_)),
           w.s([w.s([mn0], 'nn0cnd', '( %s -> M e. CC )' % A0), nq], 'npcand', '( %s -> ( ( M - ( N x. %s ) ) + ( N x. %s ) ) = M )' % (A0, Q_, Q_))], 'eqtrd',
          '( %s -> ( %s + ( N x. %s ) ) = M )' % (A0, R_, Q_))
md = w.s([w.s([d['chr'], w.s([rn0, qn0], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (A0, R_, Q_))], 'jca',
               '( %s -> ( %s /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) )' % (A0, CHR, R_, Q_)), w.inst('chrsmod')], 'syl',
         '( %s -> %s = %s )' % (A0, CSUM('( %s + ( N x. %s ) )' % (R_, Q_)), CSUM(R_)))
eqm = w.s([w.s([w.s([w.s([idm], 'oveq2d', '( %s -> ( 1 ... ( %s + ( N x. %s ) ) ) = ( 1 ... M ) )' % (A0, R_, Q_))], 'sumeq1d',
                    '( %s -> %s = %s )' % (A0, CSUM('( %s + ( N x. %s )' % (R_, Q_) + ' )'), CSUM('M')))], 'eqcomd', '( %s -> %s = %s )' % (A0, CSUM('M'), CSUM('( %s + ( N x. %s ) )' % (R_, Q_)))), md],
          'eqtrd', '( %s -> %s = %s )' % (A0, CSUM('M'), CSUM(R_)))
# the bound on the residual sum
Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (A0, R_)
inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, R_)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
nxi = w.s([d['nx']], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ai, DC))
icl = chvcl(w, Ai, 'i', nxi, inn)
iab = w.s([w.s([nxi, inn], 'jca', '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ i e. NN ) )' % (Ai, DC)), w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (Ai, CHV('i')))
fin = w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (A0, R_))
ab1 = w.s([fin, icl], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ i e. ( 1 ... %s ) ( abs ` %s ) )' % (A0, CSUM(R_), R_, CHV('i')))
le1 = w.s([fin, w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHV('i'))), a1(w, Ai, '1re', '1 e. RR'), iab], 'fsumle',
          '( %s -> sum_ i e. ( 1 ... %s ) ( abs ` %s ) <_ sum_ i e. ( 1 ... %s ) 1 )' % (A0, R_, CHV('i'), R_))
cst = w.s([fin, a1(w, A0, 'ax-1cn', '1 e. CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ i e. ( 1 ... %s ) 1 = ( ( # ` ( 1 ... %s ) ) x. 1 ) )' % (A0, R_, R_))
hs = w.s([rn0, w.inst('hashfz1')], 'syl', '( %s -> ( # ` ( 1 ... %s ) ) = %s )' % (A0, R_, R_))
rc = w.s([rn0], 'nn0cnd', '( %s -> %s e. CC )' % (A0, R_))
cst2 = w.s([cst, w.s([w.s([hs], 'oveq1d', '( %s -> ( ( # ` ( 1 ... %s ) ) x. 1 ) = ( %s x. 1 ) )' % (A0, R_, R_)), w.s([rc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A0, R_, R_))],
                    'eqtrd', '( %s -> ( ( # ` ( 1 ... %s ) ) x. 1 ) = %s )' % (A0, R_, R_))], 'eqtrd', '( %s -> sum_ i e. ( 1 ... %s ) 1 = %s )' % (A0, R_, R_))
rr = w.s([rn0], 'nn0red', '( %s -> %s e. RR )' % (A0, R_))
rlt = w.s([mr, nrp, w.inst('modlt')], 'syl2anc', '( %s -> %s < N )' % (A0, R_))
rle = w.s([rr, nr, rlt], 'ltled', '( %s -> %s <_ N )' % (A0, R_))
scl = w.s([fin, icl], 'fsumcl', '( %s -> %s e. CC )' % (A0, CSUM(R_)))
abr = w.s([scl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, CSUM(R_)))
sar = w.s([fin, w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ai, CHV('i')))], 'fsumrecl', '( %s -> sum_ i e. ( 1 ... %s ) ( abs ` %s ) e. RR )' % (A0, R_, CHV('i')))
le2 = w.s([le1, cst2], 'breqtrd', '( %s -> sum_ i e. ( 1 ... %s ) ( abs ` %s ) <_ %s )' % (A0, R_, CHV('i'), R_))
t1 = w.s([abr, sar, rr, ab1, le2], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, CSUM(R_), R_))
t2 = w.s([abr, rr, nr, t1, rle], 'letrd', '( %s -> ( abs ` %s ) <_ N )' % (A0, CSUM(R_)))
w.qed([w.s([eqm], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, CSUM('M'), CSUM(R_))), t2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ N )' % (A0, CSUM('M')))
run5(w)

# ---------------------------------------------------------------- lchrcsf
w = W('lchrcsf', 'The partial sums of a nonprincipal Dirichlet character, as a bounded sequence in C4\'s '
      'partial-sum interface ( ~ abbnd ), with the bound ` N `.')
A0 = CHR
d = chrctx(w, A0)
Aq = '( %s /\\ q e. NN )' % A0
qn = w.s([], 'simpr', '( %s -> q e. NN )' % Aq)
Aqi = '( %s /\\ i e. ( 1 ... q ) )' % Aq
icl = chvcl(w, Aqi, 'i', w.s([d['nx']], 'ad2antrr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Aqi, DC)),
            w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... q ) )' % Aqi), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Aqi))
scl = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... q ) e. Fin )' % Aq), icl], 'fsumcl', '( %s -> %s e. CC )' % (Aq, CSUM('q')))
cf = w.s([scl, w.s([], 'eqid', '%s = %s' % (CSF(), CSF()))], 'fmptd', '( %s -> %s : NN --> CC )' % (A0, CSF()))
nr = w.s([d['nn']], 'nnred', '( %s -> N e. RR )' % A0)
Am = '( %s /\\ m e. NN )' % A0
mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
sub = w.s([w.s([], 'oveq2', '( q = m -> ( 1 ... q ) = ( 1 ... m ) )')], 'sumeq1d', '( q = m -> %s = %s )' % (CSUM('q'), CSUM('m')))
val = mpv(w, Am, CSF(), 'm', CSUM('m'), sub, mn, vexd(w, Am, CSUM('m'), 'sum'))
bd = w.s([w.s([w.s([d['chr']], 'adantr', '( %s -> %s )' % (Am, CHR)), w.s([mn], 'nnnn0d', '( %s -> m e. NN0 )' % Am)], 'jca',
              '( %s -> ( %s /\\ m e. NN0 ) )' % (Am, CHR)), w.inst('chrsbnd')], 'syl', '( %s -> ( abs ` %s ) <_ N )' % (Am, CSUM('m')))
bd2 = w.s([w.s([val], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (Am, CSF(), CSUM('m'))), bd], 'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ N )' % (Am, CSF()))
w.qed([cf, nr, w.s([bd2], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ N )' % (A0, CSF()))], '3jca',
      '( %s -> ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) )' % (A0, CSF(), CSF()))
run5(w)
