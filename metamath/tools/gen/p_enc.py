"""Sortie S, batch 1: encodeNat characterised (value, typing, length, digits = bits)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

L = lambda N: 'if ( %s = 0 , 0 , ( ( |_ ` ( 2 logb %s ) ) + 1 ) )' % (N, N)
X = lambda N, i: 'if ( ( ( |_ ` ( %s / ( 2 ^ %s ) ) ) mod 2 ) = 1 , 1o , (/) )' % (N, i)
MAP = lambda N: '( i e. ( 0 ..^ %s ) |-> %s )' % (L(N), X(N, 'i'))
ENC = lambda N: '( encodeNat ` %s )' % N
LEN = lambda N: '( # ` ( encodeNat ` %s ) )' % N

# ---- 1oel2o, 0el2o
w = W('1oel2o', 'true is a Boolean: 1o is an element of 2o.')
p = w.s([], 'df2o3', '2o = { (/) , 1o }'); e = w.s([], '1oex', '1o e. _V'); pr = w.s([e], 'prid2', '1o e. { (/) , 1o }')
w.qed([pr, p], 'eleqtrri', '1o e. 2o'); run(w)
w = W('0el2o', 'false is a Boolean: (/) is an element of 2o.')
p = w.s([], 'df2o3', '2o = { (/) , 1o }'); e = w.s([], '0ex', '(/) e. _V'); pr = w.s([e], 'prid1', '(/) e. { (/) , 1o }')
w.qed([pr, p], 'eleqtrri', '(/) e. 2o'); run(w)

# ---- encnatval
w = W('encnatval', 'Value of encodeNat: the word of the binary digits of N, least significant first, of length |_ log2 N _| + 1 (empty for N = 0).')
l1 = w.s([], 'id', '( n = N -> n = N )')
c, mN = w.congr(MAP('n'), {'n': 'N'}, 'n = N', {'n': l1})
assert mN == MAP('N'), mN
d = w.s([], 'df-encnat', 'encodeNat = ( n e. NN0 |-> %s )' % MAP('n'))
x = w.s([], 'ovex', '( 0 ..^ %s ) e. _V' % L('N'))
mxi = w.inst('mptexg'); mx = w.s([x, mxi], 'ax-mp', '%s e. _V' % MAP('N'))
w.qed([c, d, mx], 'fvmpt', '( N e. NN0 -> %s = %s )' % (ENC('N'), MAP('N'))); run(w)

# ---- encnatlem1: the digit mapping is a function into 2o
w = W('encnatlem1', 'Lemma for encodeNat: the digit mapping is a function into the Booleans.')
A = 'N e. NN0'; A2 = '( N e. NN0 /\\ i e. ( 0 ..^ %s ) )' % L('N')
o1 = w.s([], '1oel2o', '1o e. 2o'); o1d = w.s([o1], 'a1i', '( %s -> 1o e. 2o )' % A2)
o0 = w.s([], '0el2o', '(/) e. 2o'); o0d = w.s([o0], 'a1i', '( %s -> (/) e. 2o )' % A2)
ic = w.s([o1d, o0d], 'ifcld', '( %s -> %s e. 2o )' % (A2, X('N', 'i')))
e = w.s([], 'eqid', '%s = %s' % (MAP('N'), MAP('N')))
w.qed([ic, e], 'fmptd', '( %s -> %s : ( 0 ..^ %s ) --> 2o )' % (A, MAP('N'), L('N'))); run(w)

# ---- encnatcl
w = W('encnatcl', 'Closure of encodeNat: a word over the Booleans.')
v = w.s([], 'encnatval', '( N e. NN0 -> %s = %s )' % (ENC('N'), MAP('N')))
f = w.s([], 'encnatlem1', '( N e. NN0 -> %s : ( 0 ..^ %s ) --> 2o )' % (MAP('N'), L('N')))
iw = w.inst('iswrdi'); m = w.s([f, iw], 'syl', '( N e. NN0 -> %s e. Word 2o )' % MAP('N'))
w.qed([v, m], 'eqeltrd', '( N e. NN0 -> %s e. Word 2o )' % ENC('N')); run(w)

# ---- encnatf
w = W('encnatf', 'encodeNat is a function from the natural numbers to the words over the Booleans.')
d = w.s([], 'df-encnat', 'encodeNat = ( n e. NN0 |-> %s )' % MAP('n'))
f = w.s([], 'encnatlem1', '( n e. NN0 -> %s : ( 0 ..^ %s ) --> 2o )' % (MAP('n'), L('n')))
iw = w.inst('iswrdi'); m = w.s([f, iw], 'syl', '( n e. NN0 -> %s e. Word 2o )' % MAP('n'))
w.qed([d, m], 'fmpti', 'encodeNat : NN0 --> Word 2o'); run(w)

# ---- encnatlem3: |_ log2 N _| e. NN0 for N e. NN
w = W('encnatlem3', 'Lemma for encodeNat: the integer part of the binary logarithm of a positive integer is a nonnegative integer.')
A = 'N e. NN'
z2 = w.s([], '2z', '2 e. ZZ'); u = w.inst('uzid'); u2 = w.s([z2, u], 'ax-mp', '2 e. ( ZZ>= ` 2 )'); u2d = w.s([u2], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % A)
rp = w.s([], 'nnrp', '( %s -> N e. RR+ )' % A)
lc = w.inst('relogbzcl'); l = w.s([u2d, rp, lc], 'syl2anc', '( %s -> ( 2 logb N ) e. RR )' % A)
g1 = w.s([], 'nnge1', '( %s -> 1 <_ N )' % A)
gb = w.inst('logbge0b'); g = w.s([u2d, rp, gb], 'syl2anc', '( %s -> ( 0 <_ ( 2 logb N ) <-> 1 <_ N ) )' % A)
g0 = w.s([g1, g], 'mpbird', '( %s -> 0 <_ ( 2 logb N ) )' % A)
fl = w.inst('flge0nn0'); w.qed([l, g0, fl], 'syl2anc', '( %s -> ( |_ ` ( 2 logb N ) ) e. NN0 )' % A); run(w)

# ---- encnatlem2: the length expression is in NN0
w = W('encnatlem2', 'Lemma for encodeNat: the length expression is a nonnegative integer.')
A = 'N e. NN0'; A1 = '( N e. NN0 /\\ N = 0 )'; A2 = '( N e. NN0 /\\ N =/= 0 )'
e1 = w.s([], 'simpr', '( %s -> N = 0 )' % A1); i1 = w.s([e1], 'iftrued', '( %s -> %s = 0 )' % (A1, L('N')))
z = w.s([], '0nn0', '0 e. NN0'); zd = w.s([z], 'a1i', '( %s -> 0 e. NN0 )' % A1); c1 = w.s([i1, zd], 'eqeltrd', '( %s -> %s e. NN0 )' % (A1, L('N')))
ne = w.s([], 'simpr', '( %s -> N =/= 0 )' % A2); nn = w.s([ne], 'neneqd', '( %s -> -. N = 0 )' % A2)
i2 = w.s([nn], 'iffalsed', '( %s -> %s = ( ( |_ ` ( 2 logb N ) ) + 1 ) )' % (A2, L('N')))
en = w.s([], 'elnnne0', '( N e. NN <-> ( N e. NN0 /\\ N =/= 0 ) )'); n2 = w.s([en], 'biimpri', '( %s -> N e. NN )' % A2)
l3 = w.inst('encnatlem3'); fl = w.s([n2, l3], 'syl', '( %s -> ( |_ ` ( 2 logb N ) ) e. NN0 )' % A2)
p1 = w.inst('peano2nn0'); fl1 = w.s([fl, p1], 'syl', '( %s -> ( ( |_ ` ( 2 logb N ) ) + 1 ) e. NN0 )' % A2)
c2 = w.s([i2, fl1], 'eqeltrd', '( %s -> %s e. NN0 )' % (A2, L('N')))
w.qed([c1, c2], 'pm2.61dane', '( %s -> %s e. NN0 )' % (A, L('N'))); run(w)

# ---- encnatlen (if form)
w = W('encnatlen', 'Length of encodeNat: |_ log2 N _| + 1 for N =/= 0 and 0 for N = 0.')
A = 'N e. NN0'
v = w.s([], 'encnatval', '( %s -> %s = %s )' % (A, ENC('N'), MAP('N')))
vh = w.s([v], 'fveq2d', '( %s -> %s = ( # ` %s ) )' % (A, LEN('N'), MAP('N')))
f = w.s([], 'encnatlem1', '( %s -> %s : ( 0 ..^ %s ) --> 2o )' % (A, MAP('N'), L('N')))
ffn = w.inst('ffn'); fn = w.s([f, ffn], 'syl', '( %s -> %s Fn ( 0 ..^ %s ) )' % (A, MAP('N'), L('N')))
hf = w.inst('hashfn'); h1 = w.s([fn, hf], 'syl', '( %s -> ( # ` %s ) = ( # ` ( 0 ..^ %s ) ) )' % (A, MAP('N'), L('N')))
l2 = w.s([], 'encnatlem2', '( %s -> %s e. NN0 )' % (A, L('N')))
hz = w.inst('hashfzo0'); h2 = w.s([l2, hz], 'syl', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (A, L('N'), L('N')))
h3 = w.s([h1, h2], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (A, MAP('N'), L('N')))
w.qed([vh, h3], 'eqtrd', '( %s -> %s = %s )' % (A, LEN('N'), L('N'))); run(w)

# ---- encnat0, encnatlen0, encnatlenn
w = W('encnat0', 'encodeNat of 0 is the empty word (Lean: encodeNat 0 = []).')
z = w.s([], '0nn0', '0 e. NN0'); v = w.s([], 'encnatval', '( 0 e. NN0 -> %s = %s )' % (ENC('0'), MAP('0')))
v2 = w.s([z, v], 'ax-mp', '%s = %s' % (ENC('0'), MAP('0')))
e = w.s([], 'eqid', '0 = 0'); it = w.s([e], 'iftruei', '%s = 0' % L('0'))
o = w.s([it], 'oveq2i', '( 0 ..^ %s ) = ( 0 ..^ 0 )' % L('0')); f0 = w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)'); o2 = w.s([o, f0], 'eqtri', '( 0 ..^ %s ) = (/)' % L('0'))
m = w.s([o2], 'mpteq1i', '%s = ( i e. (/) |-> %s )' % (MAP('0'), X('0', 'i'))); m0 = w.s([], 'mpt0', '( i e. (/) |-> %s ) = (/)' % X('0', 'i'))
m2 = w.s([m, m0], 'eqtri', '%s = (/)' % MAP('0'))
w.qed([v2, m2], 'eqtri', '%s = (/)' % ENC('0')); run(w)

w = W('encnatlen0', 'The length of encodeNat 0 is 0 (Lean: encodeNat_length_zero).')
e = w.s([], 'encnat0', '%s = (/)' % ENC('0')); h = w.s([e], 'fveq2i', '%s = ( # ` (/) )' % LEN('0')); h0 = w.s([], 'hash0', '( # ` (/) ) = 0')
w.qed([h, h0], 'eqtri', '%s = 0' % LEN('0')); run(w)

w = W('encnatlenn', 'The length of encodeNat N for N >= 1 is |_ log2 N _| + 1 (Lean: encodeNat_length).')
A = 'N e. NN'
n0 = w.s([], 'nnnn0', '( %s -> N e. NN0 )' % A); li = w.inst('encnatlen'); l = w.s([n0, li], 'syl', '( %s -> %s = %s )' % (A, LEN('N'), L('N')))
ne = w.s([], 'nnne0', '( %s -> N =/= 0 )' % A); nn = w.s([ne], 'neneqd', '( %s -> -. N = 0 )' % A)
i2 = w.s([nn], 'iffalsed', '( %s -> %s = ( ( |_ ` ( 2 logb N ) ) + 1 ) )' % (A, L('N')))
w.qed([l, i2], 'eqtrd', '( %s -> %s = ( ( |_ ` ( 2 logb N ) ) + 1 ) )' % (A, LEN('N'))); run(w)

# ---- encnatfv: the I-th digit
w = W('encnatfv', 'The I-th letter of encodeNat N: the I-th binary digit of N as a Boolean.')
A = '( N e. NN0 /\\ I e. ( 0 ..^ %s ) )' % LEN('N')
n = w.s([], 'simpl', '( %s -> N e. NN0 )' % A); ii = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ %s ) )' % (A, LEN('N')))
vi = w.inst('encnatval'); v = w.s([n, vi], 'syl', '( %s -> %s = %s )' % (A, ENC('N'), MAP('N')))
li = w.inst('encnatlen'); l = w.s([n, li], 'syl', '( %s -> %s = %s )' % (A, LEN('N'), L('N')))
dom = w.s([l], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (A, LEN('N'), L('N')))
i2 = w.s([ii, dom], 'eleqtrd', '( %s -> I e. ( 0 ..^ %s ) )' % (A, L('N')))
A3 = '( %s /\\ i = I )' % A
l1 = w.s([], 'simpr', '( %s -> i = I )' % A3)
c, xI = w.congr(X('N', 'i'), {'i': 'I'}, A3, {'i': l1}); assert xI == X('N', 'I'), xI
o1 = w.s([], '1oex', '1o e. _V'); o1d = w.s([o1], 'a1i', '( %s -> 1o e. _V )' % A)
o0 = w.s([], '0ex', '(/) e. _V'); o0d = w.s([o0], 'a1i', '( %s -> (/) e. _V )' % A)
ie = w.inst('ifexg'); sx = w.s([o1d, o0d, ie], 'syl2anc', '( %s -> %s e. _V )' % (A, X('N', 'I')))
w.qed([v, c, i2, sx], 'fvmptd', '( %s -> ( %s ` I ) = %s )' % (A, ENC('N'), X('N', 'I'))); run(w)

# ---- encnatbits: the I-th letter is true iff I is a bit of N
w = W('encnatbits', 'The I-th letter of encodeNat N is true if and only if I is a binary digit of N (set.mm\'s bits).')
A = '( N e. NN0 /\\ I e. ( 0 ..^ %s ) )' % LEN('N')
FL = '( |_ ` ( N / ( 2 ^ I ) ) )'
n = w.s([], 'simpl', '( %s -> N e. NN0 )' % A); ii = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ %s ) )' % (A, LEN('N')))
fv = w.s([], 'encnatfv', '( %s -> ( %s ` I ) = %s )' % (A, ENC('N'), X('N', 'I')))
eq1 = w.s([fv], 'eqeq1d', '( %s -> ( ( %s ` I ) = 1o <-> %s = 1o ) )' % (A, ENC('N'), X('N', 'I')))
n0 = w.s([], '1n0', '1o =/= (/)'); tb = w.inst('iftrueb'); t = w.s([n0, tb], 'ax-mp', '( %s = 1o <-> ( %s mod 2 ) = 1 )' % (X('N', 'I'), FL))
td = w.s([t], 'a1i', '( %s -> ( %s = 1o <-> ( %s mod 2 ) = 1 ) )' % (A, X('N', 'I'), FL))
b1 = w.s([eq1, td], 'bitrd', '( %s -> ( ( %s ` I ) = 1o <-> ( %s mod 2 ) = 1 ) )' % (A, ENC('N'), FL))
inn = w.inst('elfzonn0'); i0 = w.s([ii, inn], 'syl', '( %s -> I e. NN0 )' % A)
nr = w.s([n], 'nn0red', '( %s -> N e. RR )' % A)
r2 = w.s([], '2rp', '2 e. RR+'); r2d = w.s([r2], 'a1i', '( %s -> 2 e. RR+ )' % A); iz = w.s([i0], 'nn0zd', '( %s -> I e. ZZ )' % A)
pe = w.inst('rpexpcl'); p2 = w.s([r2d, iz, pe], 'syl2anc', '( %s -> ( 2 ^ I ) e. RR+ )' % A)
dv = w.inst('rerpdivcl'); q = w.s([nr, p2, dv], 'syl2anc', '( %s -> ( N / ( 2 ^ I ) ) e. RR )' % A)
fl = w.s([q], 'flcld', '( %s -> %s e. ZZ )' % (A, FL))
m2 = w.inst('mod2eq1n2dvds'); m = w.s([fl, m2], 'syl', '( %s -> ( ( %s mod 2 ) = 1 <-> -. 2 || %s ) )' % (A, FL, FL))
b2 = w.s([b1, m], 'bitrd', '( %s -> ( ( %s ` I ) = 1o <-> -. 2 || %s ) )' % (A, ENC('N'), FL))
nz = w.s([n], 'nn0zd', '( %s -> N e. ZZ )' % A)
bv = w.inst('bitsval2'); b = w.s([nz, i0, bv], 'syl2anc', '( %s -> ( I e. ( bits ` N ) <-> -. 2 || %s ) )' % (A, FL))
w.qed([b2, b], 'bitr4d', '( %s -> ( ( %s ` I ) = 1o <-> I e. ( bits ` N ) ) )' % (A, ENC('N'))); run(w)
