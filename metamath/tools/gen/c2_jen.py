"""Sortie C2 section 3.4: Jensen's inequality on a rectangle."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

FZ = '( 1 ... N )'
TERM = '( U - ( H ` k ) )'
ATERM = '( abs ` %s )' % TERM
PRD = 'prod_ k e. %s %s' % (FZ, TERM)
PRA = 'prod_ k e. %s %s' % (FZ, ATERM)
BASE = '( N e. NN /\\ H : NN --> CC /\\ U e. CC )'


def setup(w, A0):
    A1 = '( %s /\\ k e. %s )' % (A0, FZ)
    A2 = '( %s /\\ k e. NN )' % A0
    nn = w.s([], 'simp1l', '( %s -> N e. NN )' % A0)
    hf = w.s([], 'simp1r', '( %s -> H : NN --> CC )' % A0) if False else None
    return A1, A2


# ---- jenprd ----------------------------------------------------------------
w = W('jenprd', 'A lower bound on the distances gives a lower bound on the modulus of the product.')
ALLJ = 'A. j e. %s S <_ ( abs ` ( U - ( H ` j ) ) )' % FZ
A0 = '( %s /\\ ( S e. RR /\\ 0 <_ S /\\ %s ) )' % (BASE, ALLJ)
A1 = '( %s /\\ k e. %s )' % (A0, FZ)
A2 = '( %s /\\ k e. NN )' % A0
bs = w.s([], 'simpl', '( %s -> %s )' % (A0, BASE))
nn = w.s([bs, w.inst('simp1')], 'syl', '( %s -> N e. NN )' % A0)
hf = w.s([bs, w.inst('simp2')], 'syl', '( %s -> H : NN --> CC )' % A0)
uc = w.s([bs, w.inst('simp3')], 'syl', '( %s -> U e. CC )' % A0)
sa = w.s([], 'simpr', '( %s -> ( S e. RR /\\ 0 <_ S /\\ %s ) )' % (A0, ALLJ))
sr = w.s([sa, w.inst('simp1')], 'syl', '( %s -> S e. RR )' % A0)
s0 = w.s([sa, w.inst('simp2')], 'syl', '( %s -> 0 <_ S )' % A0)
allj = w.s([sa, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, ALLJ))
nn0 = w.s([nn, w.inst('nnnn0')], 'syl', '( %s -> N e. NN0 )' % A0)
fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZ))
nfk = w.s([], 'nfv', 'F/ k %s' % A0)
# body closures on ( 1 ... N )
kfz = w.s([], 'simpr', '( %s -> k e. %s )' % (A1, FZ))
knn = w.s([kfz, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % A1)
hk = w.s([w.s([hf], 'adantr', '( %s -> H : NN --> CC )' % A1), knn], 'ffvelcdmd', '( %s -> ( H ` k ) e. CC )' % A1)
tc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % A1), hk], 'subcld', '( %s -> %s e. CC )' % (A1, TERM))
atr = w.s([tc], 'abscld', '( %s -> %s e. RR )' % (A1, ATERM))
at0 = w.s([tc], 'absge0d', '( %s -> 0 <_ %s )' % (A1, ATERM))
subj = w.s([w.s([w.s([w.s([], 'fveq2', '( j = k -> ( H ` j ) = ( H ` k ) )')], 'oveq2d', '( j = k -> ( U - ( H ` j ) ) = %s )' % TERM)], 'fveq2d',
                '( j = k -> ( abs ` ( U - ( H ` j ) ) ) = %s )' % ATERM)], 'breq2d',
           '( j = k -> ( S <_ ( abs ` ( U - ( H ` j ) ) ) <-> S <_ %s ) )' % ATERM)
sle = w.s([subj, w.s([allj], 'adantr', '( %s -> %s )' % (A1, ALLJ)), kfz], 'rspcdva', '( %s -> S <_ %s )' % (A1, ATERM))
prle = w.s([nfk, fin, w.s([sr], 'adantr', '( %s -> S e. RR )' % A1), w.s([s0], 'adantr', '( %s -> 0 <_ S )' % A1), atr, sle], 'fprodle',
           '( %s -> prod_ k e. %s S <_ %s )' % (A0, FZ, PRA))
pcst = w.s([fin, w.s([sr], 'recnd', '( %s -> S e. CC )' % A0), w.inst('fprodconst')], 'syl2anc',
           '( %s -> prod_ k e. %s S = ( S ^ ( # ` %s ) ) )' % (A0, FZ, FZ))
hfz = w.s([nn0, w.inst('hashfz1')], 'syl', '( %s -> ( # ` %s ) = N )' % (A0, FZ))
pcst2 = w.s([pcst, w.s([hfz], 'oveq2d', '( %s -> ( S ^ ( # ` %s ) ) = ( S ^ N ) )' % (A0, FZ))], 'eqtrd',
            '( %s -> prod_ k e. %s S = ( S ^ N ) )' % (A0, FZ))
# closure on NN for fprodabs
knn2 = w.s([], 'simpr', '( %s -> k e. NN )' % A2)
hk2 = w.s([w.s([hf], 'adantr', '( %s -> H : NN --> CC )' % A2), knn2], 'ffvelcdmd', '( %s -> ( H ` k ) e. CC )' % A2)
tc2 = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % A2), hk2], 'subcld', '( %s -> %s e. CC )' % (A2, TERM))
nuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
nnn = w.s([nn], 'idi', '( %s -> N e. NN )' % A0)
pabs = w.s([nuz, nnn, tc2], 'fprodabs', '( %s -> ( abs ` %s ) = %s )' % (A0, PRD, PRA))
w.qed([w.s([w.s([pcst2], 'eqcomd', '( %s -> ( S ^ N ) = prod_ k e. %s S )' % (A0, FZ)), prle], 'eqbrtrd', '( %s -> ( S ^ N ) <_ %s )' % (A0, PRA)),
       w.s([pabs], 'eqcomd', '( %s -> %s = ( abs ` %s ) )' % (A0, PRA, PRD))], 'breqtrd', '( %s -> ( S ^ N ) <_ ( abs ` %s ) )' % (A0, PRD)); run1(w)

# ---- jenprd2 ---------------------------------------------------------------
w = W('jenprd2', 'An upper bound on the distances gives an upper bound on the modulus of the product.')
ALLJ = 'A. j e. %s ( abs ` ( U - ( H ` j ) ) ) <_ R' % FZ
A0 = '( %s /\\ ( R e. RR /\\ %s ) )' % (BASE, ALLJ)
A1 = '( %s /\\ k e. %s )' % (A0, FZ)
A2 = '( %s /\\ k e. NN )' % A0
bs = w.s([], 'simpl', '( %s -> %s )' % (A0, BASE))
nn = w.s([bs, w.inst('simp1')], 'syl', '( %s -> N e. NN )' % A0)
hf = w.s([bs, w.inst('simp2')], 'syl', '( %s -> H : NN --> CC )' % A0)
uc = w.s([bs, w.inst('simp3')], 'syl', '( %s -> U e. CC )' % A0)
ra = w.s([], 'simpr', '( %s -> ( R e. RR /\\ %s ) )' % (A0, ALLJ))
rr = w.s([ra, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
allj = w.s([ra, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALLJ))
nn0 = w.s([nn, w.inst('nnnn0')], 'syl', '( %s -> N e. NN0 )' % A0)
fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZ))
nfk = w.s([], 'nfv', 'F/ k %s' % A0)
kfz = w.s([], 'simpr', '( %s -> k e. %s )' % (A1, FZ))
knn = w.s([kfz, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % A1)
hk = w.s([w.s([hf], 'adantr', '( %s -> H : NN --> CC )' % A1), knn], 'ffvelcdmd', '( %s -> ( H ` k ) e. CC )' % A1)
tc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % A1), hk], 'subcld', '( %s -> %s e. CC )' % (A1, TERM))
atr = w.s([tc], 'abscld', '( %s -> %s e. RR )' % (A1, ATERM))
at0 = w.s([tc], 'absge0d', '( %s -> 0 <_ %s )' % (A1, ATERM))
subj = w.s([w.s([w.s([w.s([], 'fveq2', '( j = k -> ( H ` j ) = ( H ` k ) )')], 'oveq2d', '( j = k -> ( U - ( H ` j ) ) = %s )' % TERM)], 'fveq2d',
                '( j = k -> ( abs ` ( U - ( H ` j ) ) ) = %s )' % ATERM)], 'breq1d',
           '( j = k -> ( ( abs ` ( U - ( H ` j ) ) ) <_ R <-> %s <_ R ) )' % ATERM)
rle = w.s([subj, w.s([allj], 'adantr', '( %s -> %s )' % (A1, ALLJ)), kfz], 'rspcdva', '( %s -> %s <_ R )' % (A1, ATERM))
prle = w.s([nfk, fin, atr, at0, w.s([rr], 'adantr', '( %s -> R e. RR )' % A1), rle], 'fprodle',
           '( %s -> %s <_ prod_ k e. %s R )' % (A0, PRA, FZ))
pcst = w.s([fin, w.s([rr], 'recnd', '( %s -> R e. CC )' % A0), w.inst('fprodconst')], 'syl2anc',
           '( %s -> prod_ k e. %s R = ( R ^ ( # ` %s ) ) )' % (A0, FZ, FZ))
hfz = w.s([nn0, w.inst('hashfz1')], 'syl', '( %s -> ( # ` %s ) = N )' % (A0, FZ))
pcst2 = w.s([pcst, w.s([hfz], 'oveq2d', '( %s -> ( R ^ ( # ` %s ) ) = ( R ^ N ) )' % (A0, FZ))], 'eqtrd',
            '( %s -> prod_ k e. %s R = ( R ^ N ) )' % (A0, FZ))
knn2 = w.s([], 'simpr', '( %s -> k e. NN )' % A2)
hk2 = w.s([w.s([hf], 'adantr', '( %s -> H : NN --> CC )' % A2), knn2], 'ffvelcdmd', '( %s -> ( H ` k ) e. CC )' % A2)
tc2 = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % A2), hk2], 'subcld', '( %s -> %s e. CC )' % (A2, TERM))
nuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
pabs = w.s([nuz, nn, tc2], 'fprodabs', '( %s -> ( abs ` %s ) = %s )' % (A0, PRD, PRA))
w.qed([w.s([pabs, prle], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ prod_ k e. %s R )' % (A0, PRD, FZ)), pcst2], 'breqtrd',
      '( %s -> ( abs ` %s ) <_ ( R ^ N ) )' % (A0, PRD)); run1(w)

# ---- jenprc ----------------------------------------------------------------
w = W('jenprc', 'The product of the linear factors is a complex number.')
A0 = BASE
A1 = '( %s /\\ k e. %s )' % (A0, FZ)
nn = w.s([], 'simp1', '( %s -> N e. NN )' % A0)
hf = w.s([], 'simp2', '( %s -> H : NN --> CC )' % A0)
uc = w.s([], 'simp3', '( %s -> U e. CC )' % A0)
kfz = w.s([], 'simpr', '( %s -> k e. %s )' % (A1, FZ))
hk = w.s([w.s([hf], 'adantr', '( %s -> H : NN --> CC )' % A1), w.s([kfz, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % A1)], 'ffvelcdmd',
         '( %s -> ( H ` k ) e. CC )' % A1)
tc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % A1), hk], 'subcld', '( %s -> %s e. CC )' % (A1, TERM))
w.qed([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZ)), tc], 'fprodcl', '( %s -> %s e. CC )' % (A0, PRD)); run1(w)

# ---- rectintjen ------------------------------------------------------------
HOLG_ = HOLG('G')
HOLDG = '( %s /\\ ( A crect B ) C_ D )' % HOLG_


def PR(X, x='k'):
    return 'prod_ %s e. %s ( %s - ( H ` %s ) )' % (x, FZ, X, x)


PFAC = 'A. w e. ( A crect B ) ( F ` w ) = ( ( G ` w ) x. %s )' % PR('w')
QR = 'A. j e. %s ( abs ` ( P - ( H ` j ) ) ) <_ R' % FZ
QS = 'A. v e. %s A. j e. %s S <_ ( abs ` ( v - ( H ` j ) ) )' % (FR, FZ)
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
BASEJ = '( %s /\\ %s /\\ %s )' % (AB, INTP, HOLDG)
FAM = '( ( N e. NN /\\ H : NN --> CC ) /\\ %s )' % PFAC
BNDS = '( ( R e. RR+ /\\ %s ) /\\ ( S e. RR+ /\\ %s ) /\\ ( M e. RR /\\ %s ) )' % (QR, QS, ALF)
SN = '( S ^ N )'; RN = '( R ^ N )'
w = W('rectintjen', 'Jensen inequality on a rectangle: the modulus at an interior point of a function that factors as a holomorphic function times a product of linear factors is bounded by the frame bound times the ratio of the distance bounds, raised to the number of factors.')
A0 = '( %s /\\ %s /\\ %s )' % (BASEJ, FAM, BNDS)
At = '( %s /\\ t e. %s )' % (A0, FR)
bj = w.s([], 'simp1', '( %s -> %s )' % (A0, BASEJ))
fam = w.s([], 'simp2', '( %s -> %s )' % (A0, FAM))
bnd = w.s([], 'simp3', '( %s -> %s )' % (A0, BNDS))
ab = w.s([bj, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
it = w.s([bj, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTP))
hd = w.s([bj, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLDG))
hl = w.s([hd, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOLG_))
rdd = w.s([hd, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
nh = w.s([fam, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ H : NN --> CC ) )' % A0)
pfac = w.s([fam, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, PFAC))
nn = w.s([nh, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
hf = w.s([nh, w.inst('simpr')], 'syl', '( %s -> H : NN --> CC )' % A0)
rb = w.s([bnd, w.inst('simp1')], 'syl', '( %s -> ( R e. RR+ /\\ %s ) )' % (A0, QR))
sb = w.s([bnd, w.inst('simp2')], 'syl', '( %s -> ( S e. RR+ /\\ %s ) )' % (A0, QS))
mb = w.s([bnd, w.inst('simp3')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
rrp = w.s([rb, w.inst('simpl')], 'syl', '( %s -> R e. RR+ )' % A0)
qr = w.s([rb, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, QR))
srp = w.s([sb, w.inst('simpl')], 'syl', '( %s -> S e. RR+ )' % A0)
qs = w.s([sb, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, QS))
mr = w.s([mb, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
alf = w.s([mb, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
nz = w.s([nn], 'nnzd', '( %s -> N e. ZZ )' % A0)
snrp = w.s([srp, nz], 'rpexpcld', '( %s -> %s e. RR+ )' % (A0, SN))
rnrp = w.s([rrp, nz], 'rpexpcld', '( %s -> %s e. RR+ )' % (A0, RN))
snr = w.s([snrp], 'rpred', '( %s -> %s e. RR )' % (A0, SN))
rnr = w.s([rnrp], 'rpred', '( %s -> %s e. RR )' % (A0, RN))
msn = w.s([mr, snrp], 'rerpdivcld', '( %s -> ( M / %s ) e. RR )' % (A0, SN))
gcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
gff = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A0)
fcn = None
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
      [('simpll', '%s < %s' % (RA, RP)), ('simplr', '%s < %s' % (RP, RB)),
       ('simprl', '%s < %s' % (IA, IP)), ('simprr', '%s < %s' % (IP, IB))]]
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr_ = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP)); pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
geo = w.s([w.s([w.s([ar, pr_, br, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB)),
           w.s([w.s([ai, pi_, bi, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))],
          'jca', '( %s -> %s )' % (A0, GEO))
fru = w.s([ab, geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, FR))


def lt_(st, form):
    return w.s([st], 'adantr', '( %s -> %s )' % (At, form))


tf = w.s([], 'simpr', '( %s -> t e. %s )' % (At, FR))
tr_ = w.s([lt_(fru, '%s C_ ( A crect B )' % FR), tf], 'sseldd', '( %s -> t e. ( A crect B ) )' % At)
td = w.s([lt_(rdd, '( A crect B ) C_ D'), tr_], 'sseldd', '( %s -> t e. D )' % At)
tc = w.s([lt_(w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0), '( A crect B ) C_ CC'), tr_], 'sseldd', '( %s -> t e. CC )' % At)
# PFAC at t
pw1 = w.s([], 'fveq2', '( w = t -> ( F ` w ) = ( F ` t ) )')
pw2 = w.s([], 'fveq2', '( w = t -> ( G ` w ) = ( G ` t ) )')
pw3 = w.s([w.s([w.s([], 'oveq1', '( w = t -> ( w - ( H ` k ) ) = ( t - ( H ` k ) ) )')], 'adantr',
                '( ( w = t /\\ k e. %s ) -> ( w - ( H ` k ) ) = ( t - ( H ` k ) ) )' % FZ)], 'prodeq2dv',
           '( w = t -> %s = %s )' % (PR('w'), PR('t')))
pw4 = w.s([pw2, pw3], 'oveq12d', '( w = t -> ( ( G ` w ) x. %s ) = ( ( G ` t ) x. %s ) )' % (PR('w'), PR('t')))
subw = w.s([pw1, pw4], 'eqeq12d', '( w = t -> ( ( F ` w ) = ( ( G ` w ) x. %s ) <-> ( F ` t ) = ( ( G ` t ) x. %s ) ) )' % (PR('w'), PR('t')))
fact = w.s([subw, lt_(pfac, PFAC), tr_], 'rspcdva', '( %s -> ( F ` t ) = ( ( G ` t ) x. %s ) )' % (At, PR('t')))
# the distance bound at t
qv1 = w.s([w.s([w.s([], 'oveq1', '( v = t -> ( v - ( H ` j ) ) = ( t - ( H ` j ) ) )')], 'fveq2d',
               '( v = t -> ( abs ` ( v - ( H ` j ) ) ) = ( abs ` ( t - ( H ` j ) ) ) )')], 'breq2d',
          '( v = t -> ( S <_ ( abs ` ( v - ( H ` j ) ) ) <-> S <_ ( abs ` ( t - ( H ` j ) ) ) ) )')
qv2 = w.s([qv1], 'ralbidv', '( v = t -> ( A. j e. %s S <_ ( abs ` ( v - ( H ` j ) ) ) <-> A. j e. %s S <_ ( abs ` ( t - ( H ` j ) ) ) ) )' % (FZ, FZ))
qst = w.s([qv2, lt_(qs, QS), tf], 'rspcdva', '( %s -> A. j e. %s S <_ ( abs ` ( t - ( H ` j ) ) ) )' % (At, FZ))
jp = w.s([w.s([lt_(nn, 'N e. NN'), lt_(hf, 'H : NN --> CC'), tc], '3jca', '( %s -> ( N e. NN /\\ H : NN --> CC /\\ t e. CC ) )' % At),
          w.s([lt_(w.s([srp], 'rpred', '( %s -> S e. RR )' % A0), 'S e. RR'), lt_(w.s([srp], 'rpge0d', '( %s -> 0 <_ S )' % A0), '0 <_ S'), qst], '3jca',
              '( %s -> ( S e. RR /\\ 0 <_ S /\\ A. j e. %s S <_ ( abs ` ( t - ( H ` j ) ) ) ) )' % (At, FZ)), w.inst('jenprd')], 'syl2anc',
         '( %s -> %s <_ ( abs ` %s ) )' % (At, SN, PR('t')))
# abs of the factorisation at t
gtc = w.s([lt_(gff, 'G : D --> CC'), td], 'ffvelcdmd', '( %s -> ( G ` t ) e. CC )' % At)
Atk = '( %s /\\ k e. %s )' % (At, FZ)
kfz = w.s([], 'simpr', '( %s -> k e. %s )' % (Atk, FZ))
hkt = w.s([w.s([lt_(hf, 'H : NN --> CC')], 'adantr', '( %s -> H : NN --> CC )' % Atk), w.s([kfz, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Atk)],
          'ffvelcdmd', '( %s -> ( H ` k ) e. CC )' % Atk)
ttc = w.s([w.s([tc], 'adantr', '( %s -> t e. CC )' % Atk), hkt], 'subcld', '( %s -> ( t - ( H ` k ) ) e. CC )' % Atk)
prtc = w.s([lt_(nn, 'N e. NN'), lt_(hf, 'H : NN --> CC'), tc, w.inst('jenprc')], 'syl3anc', '( %s -> %s e. CC )' % (At, PR('t')))
abst = w.s([w.s([fact], 'fveq2d', '( %s -> ( abs ` ( F ` t ) ) = ( abs ` ( ( G ` t ) x. %s ) ) )' % (At, PR('t'))),
            w.s([gtc, prtc], 'absmuld', '( %s -> ( abs ` ( ( G ` t ) x. %s ) ) = ( ( abs ` ( G ` t ) ) x. ( abs ` %s ) ) )' % (At, PR('t'), PR('t')))],
           'eqtrd', '( %s -> ( abs ` ( F ` t ) ) = ( ( abs ` ( G ` t ) ) x. ( abs ` %s ) ) )' % (At, PR('t')))
agt = w.s([gtc], 'abscld', '( %s -> ( abs ` ( G ` t ) ) e. RR )' % At)
agt0 = w.s([gtc], 'absge0d', '( %s -> 0 <_ ( abs ` ( G ` t ) ) )' % At)
aprt = w.s([prtc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, PR('t')))
mul1 = w.s([w.s([lt_(snr, '%s e. RR' % SN), aprt, w.s([agt, agt0], 'jca', '( %s -> ( ( abs ` ( G ` t ) ) e. RR /\\ 0 <_ ( abs ` ( G ` t ) ) ) )' % At)], '3jca',
                '( %s -> ( %s e. RR /\\ ( abs ` %s ) e. RR /\\ ( ( abs ` ( G ` t ) ) e. RR /\\ 0 <_ ( abs ` ( G ` t ) ) ) ) )' % (At, SN, PR('t'))),
            jp, w.inst('lemul2a')], 'syl2anc',
           '( %s -> ( ( abs ` ( G ` t ) ) x. %s ) <_ ( ( abs ` ( G ` t ) ) x. ( abs ` %s ) ) )' % (At, SN, PR('t')))
subu = w.s([w.s([w.s([], 'fveq2', '( u = t -> ( F ` u ) = ( F ` t ) )')], 'fveq2d', '( u = t -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` t ) ) )')], 'breq1d',
           '( u = t -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` t ) ) <_ M ) )')
mbt = w.s([subu, lt_(alf, ALF), tf], 'rspcdva', '( %s -> ( abs ` ( F ` t ) ) <_ M )' % At)
mul2 = w.s([mul1, w.s([abst], 'eqcomd', '( %s -> ( ( abs ` ( G ` t ) ) x. ( abs ` %s ) ) = ( abs ` ( F ` t ) ) )' % (At, PR('t')))], 'breqtrd',
           '( %s -> ( ( abs ` ( G ` t ) ) x. %s ) <_ ( abs ` ( F ` t ) ) )' % (At, SN))
mul3 = w.s([w.s([agt, lt_(snr, '%s e. RR' % SN)], 'remulcld', '( %s -> ( ( abs ` ( G ` t ) ) x. %s ) e. RR )' % (At, SN)),
            w.s([gtc, prtc], 'absmuld', '( %s -> ( abs ` ( ( G ` t ) x. %s ) ) = ( ( abs ` ( G ` t ) ) x. ( abs ` %s ) ) )' % (At, PR('t'), PR('t')))], 'idi',
           '( %s -> ( ( abs ` ( G ` t ) ) x. %s ) e. RR )' % (At, SN)) if False else w.s([agt, lt_(snr, '%s e. RR' % SN)], 'remulcld',
           '( %s -> ( ( abs ` ( G ` t ) ) x. %s ) e. RR )' % (At, SN))
aft = w.s([w.s([lt_(w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A0), 'G : D --> CC')], 'idi', '( %s -> G : D --> CC )' % At)], 'idi', '( %s -> G : D --> CC )' % At) if False else None
mult = w.s([mul3, agt, lt_(mr, 'M e. RR'), mul2, mbt], 'idi', 'x') if False else None
mle = w.s([mul3, w.s([w.s([lt_(mr, 'M e. RR')], 'idi', '( %s -> M e. RR )' % At)], 'idi', '( %s -> M e. RR )' % At)], 'idi', 'y') if False else None
mchain = w.s([mul3, w.s([gtc, prtc], 'absmuld', 'dummy')], 'idi', 'z') if False else None
tot = w.s([mul3, w.s([lt_(mr, 'M e. RR')], 'idi', '( %s -> M e. RR )' % At)], 'idi', 'q') if False else None
step = w.s([mul3, w.s([gtc], 'abscld', '( %s -> ( abs ` ( F ` t ) ) e. RR )' % At)], 'idi', 'r') if False else None
absft = w.s([w.s([lt_(w.s([mr], 'idi', '( %s -> M e. RR )' % A0), 'M e. RR')], 'idi', '( %s -> M e. RR )' % At)], 'idi', '( %s -> M e. RR )' % At) if False else lt_(mr, 'M e. RR')
aftr = w.s([w.s([gtc, prtc], 'mulcld', '( %s -> ( ( G ` t ) x. %s ) e. CC )' % (At, PR('t')))], 'abscld', '( %s -> ( abs ` ( ( G ` t ) x. %s ) ) e. RR )' % (At, PR('t')))
ftr = w.s([w.s([abst, w.s([gtc, prtc], 'absmuld', '( %s -> ( abs ` ( ( G ` t ) x. %s ) ) = ( ( abs ` ( G ` t ) ) x. ( abs ` %s ) ) )' % (At, PR('t'), PR('t')))], 'eqtr4d',
                '( %s -> ( abs ` ( F ` t ) ) = ( abs ` ( ( G ` t ) x. %s ) ) )' % (At, PR('t'))), aftr], 'eqeltrd', '( %s -> ( abs ` ( F ` t ) ) e. RR )' % At)
chain = w.s([mul3, ftr, absft, mul2, mbt], 'letrd', '( %s -> ( ( abs ` ( G ` t ) ) x. %s ) <_ M )' % (At, SN))
gdiv = w.s([chain, w.s([agt, absft, w.s([lt_(snr, '%s e. RR' % SN), lt_(w.s([snrp], 'rpgt0d', '( %s -> 0 < %s )' % (A0, SN)), '0 < %s' % SN)], 'jca',
                                        '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (At, SN, SN)), w.inst('lemuldiv')], 'syl3anc',
                       '( %s -> ( ( ( abs ` ( G ` t ) ) x. %s ) <_ M <-> ( abs ` ( G ` t ) ) <_ ( M / %s ) ) )' % (At, SN, SN))], 'mpbid',
           '( %s -> ( abs ` ( G ` t ) ) <_ ( M / %s ) )' % (At, SN))
allt = w.s([gdiv], 'ralrimiva', '( %s -> A. t e. %s ( abs ` ( G ` t ) ) <_ ( M / %s ) )' % (A0, FR, SN))
cbvu = w.s([w.s([w.s([w.s([], 'fveq2', '( t = u -> ( G ` t ) = ( G ` u ) )')], 'fveq2d', '( t = u -> ( abs ` ( G ` t ) ) = ( abs ` ( G ` u ) ) )')], 'breq1d',
                '( t = u -> ( ( abs ` ( G ` t ) ) <_ ( M / %s ) <-> ( abs ` ( G ` u ) ) <_ ( M / %s ) ) )' % (SN, SN))], 'cbvralvw',
           '( A. t e. %s ( abs ` ( G ` t ) ) <_ ( M / %s ) <-> A. u e. %s ( abs ` ( G ` u ) ) <_ ( M / %s ) )' % (FR, SN, FR, SN))
allu = w.s([allt, cbvu], 'sylib', '( %s -> A. u e. %s ( abs ` ( G ` u ) ) <_ ( M / %s ) )' % (A0, FR, SN))
mmg = w.s([ab, it, hd, w.s([msn, allu], 'jca', '( %s -> ( ( M / %s ) e. RR /\\ A. u e. %s ( abs ` ( G ` u ) ) <_ ( M / %s ) ) )' % (A0, SN, FR, SN)),
           w.inst('rectintmm')], 'syl31anc', '( %s -> ( abs ` ( G ` P ) ) <_ ( M / %s ) )' % (A0, SN))
# at P
pcr = w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)
pd = w.s([rdd, pcr], 'sseldd', '( %s -> P e. D )' % A0)
gpc = w.s([gff, pd], 'ffvelcdmd', '( %s -> ( G ` P ) e. CC )' % A0)
pp1 = w.s([], 'fveq2', '( w = P -> ( F ` w ) = ( F ` P ) )')
pp2 = w.s([], 'fveq2', '( w = P -> ( G ` w ) = ( G ` P ) )')
pp3 = w.s([w.s([w.s([], 'oveq1', '( w = P -> ( w - ( H ` k ) ) = ( P - ( H ` k ) ) )')], 'adantr',
                '( ( w = P /\\ k e. %s ) -> ( w - ( H ` k ) ) = ( P - ( H ` k ) ) )' % FZ)], 'prodeq2dv',
           '( w = P -> %s = %s )' % (PR('w'), PR('P')))
pp4 = w.s([pp2, pp3], 'oveq12d', '( w = P -> ( ( G ` w ) x. %s ) = ( ( G ` P ) x. %s ) )' % (PR('w'), PR('P')))
subp = w.s([pp1, pp4], 'eqeq12d', '( w = P -> ( ( F ` w ) = ( ( G ` w ) x. %s ) <-> ( F ` P ) = ( ( G ` P ) x. %s ) ) )' % (PR('w'), PR('P')))
facp = w.s([subp, pfac, pcr], 'rspcdva', '( %s -> ( F ` P ) = ( ( G ` P ) x. %s ) )' % (A0, PR('P')))
A0k = '( %s /\\ k e. %s )' % (A0, FZ)
kfz2 = w.s([], 'simpr', '( %s -> k e. %s )' % (A0k, FZ))
hkp = w.s([w.s([hf], 'adantr', '( %s -> H : NN --> CC )' % A0k), w.s([kfz2, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % A0k)], 'ffvelcdmd',
          '( %s -> ( H ` k ) e. CC )' % A0k)
ptc = w.s([w.s([pc], 'adantr', '( %s -> P e. CC )' % A0k), hkp], 'subcld', '( %s -> ( P - ( H ` k ) ) e. CC )' % A0k)
prpc = w.s([nn, hf, pc, w.inst('jenprc')], 'syl3anc', '( %s -> %s e. CC )' % (A0, PR('P')))
jp2 = w.s([w.s([nn, hf, pc], '3jca', '( %s -> ( N e. NN /\\ H : NN --> CC /\\ P e. CC ) )' % A0),
           w.s([w.s([rrp], 'rpred', '( %s -> R e. RR )' % A0), qr], 'jca', '( %s -> ( R e. RR /\\ %s ) )' % (A0, QR)), w.inst('jenprd2')], 'syl2anc',
          '( %s -> ( abs ` %s ) <_ %s )' % (A0, PR('P'), RN))
absp = w.s([w.s([facp], 'fveq2d', '( %s -> ( abs ` ( F ` P ) ) = ( abs ` ( ( G ` P ) x. %s ) ) )' % (A0, PR('P'))),
            w.s([gpc, prpc], 'absmuld', '( %s -> ( abs ` ( ( G ` P ) x. %s ) ) = ( ( abs ` ( G ` P ) ) x. ( abs ` %s ) ) )' % (A0, PR('P'), PR('P')))],
           'eqtrd', '( %s -> ( abs ` ( F ` P ) ) = ( ( abs ` ( G ` P ) ) x. ( abs ` %s ) ) )' % (A0, PR('P')))
agp = w.s([gpc], 'abscld', '( %s -> ( abs ` ( G ` P ) ) e. RR )' % A0)
agp0 = w.s([gpc], 'absge0d', '( %s -> 0 <_ ( abs ` ( G ` P ) ) )' % A0)
aprp = w.s([prpc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, PR('P')))
aprp0 = w.s([prpc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, PR('P')))
prod = w.s([agp, msn, aprp, rnr, agp0, aprp0, mmg, jp2], 'lemul12ad',
           '( %s -> ( ( abs ` ( G ` P ) ) x. ( abs ` %s ) ) <_ ( ( M / %s ) x. %s ) )' % (A0, PR('P'), SN, RN))
key = w.s([w.s([absp], 'idi', '( %s -> ( abs ` ( F ` P ) ) = ( ( abs ` ( G ` P ) ) x. ( abs ` %s ) ) )' % (A0, PR('P'))), prod], 'eqbrtrd',
          '( %s -> ( abs ` ( F ` P ) ) <_ ( ( M / %s ) x. %s ) )' % (A0, SN, RN))
afp = w.s([w.s([gpc, prpc], 'mulcld', '( %s -> ( ( G ` P ) x. %s ) e. CC )' % (A0, PR('P')))], 'abscld',
          '( %s -> ( abs ` ( ( G ` P ) x. %s ) ) e. RR )' % (A0, PR('P')))
afpr = w.s([w.s([absp, w.s([gpc, prpc], 'absmuld', '( %s -> ( abs ` ( ( G ` P ) x. %s ) ) = ( ( abs ` ( G ` P ) ) x. ( abs ` %s ) ) )' % (A0, PR('P'), PR('P')))], 'eqtr4d',
                '( %s -> ( abs ` ( F ` P ) ) = ( abs ` ( ( G ` P ) x. %s ) ) )' % (A0, PR('P'))), afp], 'eqeltrd', '( %s -> ( abs ` ( F ` P ) ) e. RR )' % A0)
msrn = w.s([msn, rnr], 'remulcld', '( %s -> ( ( M / %s ) x. %s ) e. RR )' % (A0, SN, RN))
mul = w.s([w.s([afpr, msrn, w.s([snr, w.s([snrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, SN))], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, SN, SN))], '3jca',
                '( %s -> ( ( abs ` ( F ` P ) ) e. RR /\\ ( ( M / %s ) x. %s ) e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A0, SN, RN, SN, SN)),
           key, w.inst('lemul1a')], 'syl2anc',
          '( %s -> ( ( abs ` ( F ` P ) ) x. %s ) <_ ( ( ( M / %s ) x. %s ) x. %s ) )' % (A0, SN, SN, RN, SN))
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
snc = w.s([snr], 'recnd', '( %s -> %s e. CC )' % (A0, SN))
rnc = w.s([rnr], 'recnd', '( %s -> %s e. CC )' % (A0, RN))
msnc = w.s([mc, snc, w.s([snrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, SN))], 'divcld', '( %s -> ( M / %s ) e. CC )' % (A0, SN))
eq1 = w.s([msnc, rnc, snc], 'mul32d', '( %s -> ( ( ( M / %s ) x. %s ) x. %s ) = ( ( ( M / %s ) x. %s ) x. %s ) )' % (A0, SN, RN, SN, SN, SN, RN))
eq2 = w.s([w.s([mc, snc, w.s([snrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, SN))], 'divcan1d', '( %s -> ( ( M / %s ) x. %s ) = M )' % (A0, SN, SN))], 'oveq1d',
          '( %s -> ( ( ( M / %s ) x. %s ) x. %s ) = ( M x. %s ) )' % (A0, SN, SN, RN, RN))
w.qed([mul, w.s([eq1, eq2], 'eqtrd', '( %s -> ( ( ( M / %s ) x. %s ) x. %s ) = ( M x. %s ) )' % (A0, SN, RN, SN, RN))], 'breqtrd',
      '( %s -> ( ( abs ` ( F ` P ) ) x. %s ) <_ ( M x. %s ) )' % (A0, SN, RN)); run1(w)

# ---- expdivlog -------------------------------------------------------------
w = W('expdivlog', 'The logarithmic form of the Jensen bound: a multiplicative inequality between powers becomes a linear inequality between logarithms.')
A0 = '( ( A e. RR+ /\\ M e. RR+ ) /\\ ( R e. RR+ /\\ S e. RR+ /\\ N e. NN0 ) /\\ ( A x. ( S ^ N ) ) <_ ( M x. ( R ^ N ) ) )'
arp = w.s([], 'simp1l', '( %s -> A e. RR+ )' % A0)
mrp = w.s([], 'simp1r', '( %s -> M e. RR+ )' % A0)
rrp = w.s([], 'simp21', '( %s -> R e. RR+ )' % A0)
srp = w.s([], 'simp22', '( %s -> S e. RR+ )' % A0)
nn0 = w.s([], 'simp23', '( %s -> N e. NN0 )' % A0)
hyp = w.s([], 'simp3', '( %s -> ( A x. ( S ^ N ) ) <_ ( M x. ( R ^ N ) ) )' % A0)
nz = w.s([nn0], 'nn0zd', '( %s -> N e. ZZ )' % A0)
snrp = w.s([srp, nz], 'rpexpcld', '( %s -> ( S ^ N ) e. RR+ )' % A0)
rnrp = w.s([rrp, nz], 'rpexpcld', '( %s -> ( R ^ N ) e. RR+ )' % A0)
ar = w.s([arp], 'rpred', '( %s -> A e. RR )' % A0)
mr = w.s([mrp], 'rpred', '( %s -> M e. RR )' % A0)
snr = w.s([snrp], 'rpred', '( %s -> ( S ^ N ) e. RR )' % A0)
rnr = w.s([rnrp], 'rpred', '( %s -> ( R ^ N ) e. RR )' % A0)
mrn = w.s([mr, rnr], 'remulcld', '( %s -> ( M x. ( R ^ N ) ) e. RR )' % A0)
d1 = w.s([hyp, w.s([snr, mrn, w.s([ar, w.s([arp], 'rpgt0d', '( %s -> 0 < A )' % A0)], 'jca', '( %s -> ( A e. RR /\\ 0 < A ) )' % A0), w.inst('lemuldiv2')],
                   'syl3anc', '( %s -> ( ( A x. ( S ^ N ) ) <_ ( M x. ( R ^ N ) ) <-> ( S ^ N ) <_ ( ( M x. ( R ^ N ) ) / A ) ) )' % A0)], 'mpbid',
         '( %s -> ( S ^ N ) <_ ( ( M x. ( R ^ N ) ) / A ) )' % A0)
mra = w.s([mrn, arp], 'rerpdivcld', '( %s -> ( ( M x. ( R ^ N ) ) / A ) e. RR )' % A0)
d2 = w.s([d1, w.s([snr, mra, rnrp], 'lediv1d', '( %s -> ( ( S ^ N ) <_ ( ( M x. ( R ^ N ) ) / A ) <-> ( ( S ^ N ) / ( R ^ N ) ) <_ ( ( ( M x. ( R ^ N ) ) / A ) / ( R ^ N ) ) ) )' % A0)],
         'mpbid', '( %s -> ( ( S ^ N ) / ( R ^ N ) ) <_ ( ( ( M x. ( R ^ N ) ) / A ) / ( R ^ N ) ) )' % A0)
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
ac = w.s([ar], 'recnd', '( %s -> A e. CC )' % A0)
rnc = w.s([rnr], 'recnd', '( %s -> ( R ^ N ) e. CC )' % A0)
ane = w.s([arp], 'rpne0d', '( %s -> A =/= 0 )' % A0)
rne = w.s([rnrp], 'rpne0d', '( %s -> ( R ^ N ) =/= 0 )' % A0)
e1 = w.s([w.s([w.s([mc, rnc, ac, ane], 'div23d', '( %s -> ( ( M x. ( R ^ N ) ) / A ) = ( ( M / A ) x. ( R ^ N ) ) )' % A0)], 'oveq1d',
               '( %s -> ( ( ( M x. ( R ^ N ) ) / A ) / ( R ^ N ) ) = ( ( ( M / A ) x. ( R ^ N ) ) / ( R ^ N ) ) )' % A0),
          w.s([w.s([mc, ac, ane], 'divcld', '( %s -> ( M / A ) e. CC )' % A0), rnc, rne], 'divcan4d',
              '( %s -> ( ( ( M / A ) x. ( R ^ N ) ) / ( R ^ N ) ) = ( M / A ) )' % A0)], 'eqtrd',
         '( %s -> ( ( ( M x. ( R ^ N ) ) / A ) / ( R ^ N ) ) = ( M / A ) )' % A0)
d3 = w.s([d2, e1], 'breqtrd', '( %s -> ( ( S ^ N ) / ( R ^ N ) ) <_ ( M / A ) )' % A0)
ed = w.s([w.s([w.s([srp], 'rpcnd', '( %s -> S e. CC )' % A0), w.s([w.s([rrp], 'rpcnd', '( %s -> R e. CC )' % A0), w.s([rrp], 'rpne0d', '( %s -> R =/= 0 )' % A0)], 'jca',
                    '( %s -> ( R e. CC /\\ R =/= 0 ) )' % A0), nn0, w.inst('expdiv')], 'syl3anc',
              '( %s -> ( ( S / R ) ^ N ) = ( ( S ^ N ) / ( R ^ N ) ) )' % A0)], 'idi',
         '( %s -> ( ( S / R ) ^ N ) = ( ( S ^ N ) / ( R ^ N ) ) )' % A0)
d4 = w.s([ed, d3], 'eqbrtrd', '( %s -> ( ( S / R ) ^ N ) <_ ( M / A ) )' % A0)
srrp = w.s([srp, rrp], 'rpdivcld', '( %s -> ( S / R ) e. RR+ )' % A0)
srnrp = w.s([srrp, nz], 'rpexpcld', '( %s -> ( ( S / R ) ^ N ) e. RR+ )' % A0)
marp = w.s([mrp, arp], 'rpdivcld', '( %s -> ( M / A ) e. RR+ )' % A0)
lg = w.s([d4, w.s([srnrp, marp], 'logled', '( %s -> ( ( ( S / R ) ^ N ) <_ ( M / A ) <-> ( log ` ( ( S / R ) ^ N ) ) <_ ( log ` ( M / A ) ) ) )' % A0)],
         'mpbid', '( %s -> ( log ` ( ( S / R ) ^ N ) ) <_ ( log ` ( M / A ) ) )' % A0)
w.qed([w.s([w.s([srrp, nz, w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( ( S / R ) ^ N ) ) = ( N x. ( log ` ( S / R ) ) ) )' % A0)], 'eqcomd',
           '( %s -> ( N x. ( log ` ( S / R ) ) ) = ( log ` ( ( S / R ) ^ N ) ) )' % A0), lg], 'eqbrtrd',
      '( %s -> ( N x. ( log ` ( S / R ) ) ) <_ ( log ` ( M / A ) ) )' % A0); run1(w)
