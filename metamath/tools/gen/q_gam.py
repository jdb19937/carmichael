"""Sortie S, batch 2: the alphabet Gamma' (finite, its letters), inclBool, encNatGam."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

GAM = "( ( { 0 , 2 } u. { 3 , 4 } ) u. ( { 1 } X. 2o ) )"
ENC = lambda N: '( encodeNat ` %s )' % N
LEN = lambda N: '( # ` ( encodeNat ` %s ) )' % N
EG = lambda N: '( encNatGam ` %s )' % N
CO = lambda N: '( inclBool o. ( encodeNat ` %s ) )' % N

# ---- gammafi, gammaex
w = W('gammafi', "The alphabet Gamma' is finite (Lean: Fintype Gamma').")
p1 = w.s([], 'prfi', '{ 0 , 2 } e. Fin'); p2 = w.s([], 'prfi', '{ 3 , 4 } e. Fin')
ui = w.inst('unfi'); u1 = w.s([p1, p2, ui], 'mp2an', '( { 0 , 2 } u. { 3 , 4 } ) e. Fin')
s1 = w.s([], 'snfi', '{ 1 } e. Fin'); o = w.s([], '2onn', '2o e. _om'); nf = w.inst('nnfi'); f2 = w.s([o, nf], 'ax-mp', '2o e. Fin')
xi = w.inst('xpfi'); x = w.s([s1, f2, xi], 'mp2an', '( { 1 } X. 2o ) e. Fin')
ui2 = w.inst('unfi'); u = w.s([u1, x, ui2], 'mp2an', '%s e. Fin' % GAM)
d = w.s([], 'df-gamma', "Gamma' = %s" % GAM)
w.qed([d, u], 'eqeltri', "Gamma' e. Fin"); run(w)

w = W('gammaex', "The alphabet Gamma' is a set.")
f = w.s([], 'gammafi', "Gamma' e. Fin"); w.qed([f], 'elexi', "Gamma' e. _V"); run(w)

# ---- the letters
def letter(label, desc, n, prtxt, prlem, ex, side):
    w = W(label, desc)
    if ex == 'c0ex':
        e = w.s([], 'c0ex', '0 e. _V')
    else:
        er = w.s([], ex, '%s e. RR' % n); e = w.s([er], 'elexi', '%s e. _V' % n)
    if prlem == 'prid1':
        pr = w.s([e], 'prid1', '%s e. %s' % (n, prtxt))
    else:
        pr = w.s([e], 'prid2', '%s e. %s' % (n, prtxt))
    ui = w.inst('elun1' if side == 1 else 'elun2')
    u1 = w.s([pr, ui], 'ax-mp', '%s e. ( { 0 , 2 } u. { 3 , 4 } )' % n)
    ui2 = w.inst('elun1'); u2 = w.s([u1, ui2], 'ax-mp', '%s e. %s' % (n, GAM))
    d = w.s([], 'df-gamma', "Gamma' = %s" % GAM)
    w.qed([u2, d], 'eleqtrri', "%s e. Gamma'" % n); run(w)
letter('gamma0', "The letter blank = 0 of Gamma'.", '0', '{ 0 , 2 }', 'prid1', 'c0ex', 1)
letter('gamma2', "The letter bra = 2 of Gamma'.", '2', '{ 0 , 2 }', 'prid2', '2re', 1)
letter('gamma3', "The letter ket = 3 of Gamma'.", '3', '{ 3 , 4 }', 'prid1', '3re', 2)
letter('gamma4', "The letter comma = 4 of Gamma'.", '4', '{ 3 , 4 }', 'prid2', '4re', 2)

# ---- bitgamma
w = W('bitgamma', "The letters bit b = <. 1 , b >. of Gamma'.")
e1 = w.s([], '1ex', '1 e. _V'); si = w.inst('snidg'); s1 = w.s([e1, si], 'ax-mp', '1 e. { 1 }')
xi = w.inst('opelxpi'); x = w.s([s1, xi], 'mpan', '( B e. 2o -> <. 1 , B >. e. ( { 1 } X. 2o ) )')
ui = w.inst('elun2'); u = w.s([x, ui], 'syl', '( B e. 2o -> <. 1 , B >. e. %s )' % GAM)
d = w.s([], 'df-gamma', "Gamma' = %s" % GAM)
w.qed([u, d], 'eleqtrrdi', "( B e. 2o -> <. 1 , B >. e. Gamma' )"); run(w)

# ---- inclboolf, inclboolfv
w = W('inclboolf', "inclBool is a function from the Booleans into Gamma'.")
d = w.s([], 'df-inclbool', 'inclBool = ( b e. 2o |-> <. 1 , b >. )')
g = w.s([], 'bitgamma', "( b e. 2o -> <. 1 , b >. e. Gamma' )")
w.qed([d, g], 'fmpti', "inclBool : 2o --> Gamma'"); run(w)

w = W('inclboolfv', 'Value of inclBool.')
c = w.s([], 'opeq2', '( b = B -> <. 1 , b >. = <. 1 , B >. )')
d = w.s([], 'df-inclbool', 'inclBool = ( b e. 2o |-> <. 1 , b >. )')
x = w.s([], 'opex', '<. 1 , B >. e. _V')
w.qed([c, d, x], 'fvmpt', '( B e. 2o -> ( inclBool ` B ) = <. 1 , B >. )'); run(w)

# ---- encnatgamval
w = W('encnatgamval', "Value of encNatGam: the letters of encodeNat N mapped into Gamma'.")
l1 = w.s([], 'id', '( n = N -> n = N )')
c, cN = w.congr(CO('n'), {'n': 'N'}, 'n = N', {'n': l1}); assert cN == CO('N'), cN
d = w.s([], 'df-encnatgam', 'encNatGam = ( n e. NN0 |-> %s )' % CO('n'))
di = w.s([], 'df-inclbool', 'inclBool = ( b e. 2o |-> <. 1 , b >. )')
o2 = w.s([], '2oex', '2o e. _V'); mi = w.inst('mptexg'); m = w.s([o2, mi], 'ax-mp', '( b e. 2o |-> <. 1 , b >. ) e. _V')
ix = w.s([di, m], 'eqeltri', 'inclBool e. _V')
fx = w.s([], 'fvex', '%s e. _V' % ENC('N'))
ci = w.inst('coexg'); cx = w.s([ix, fx, ci], 'mp2an', '%s e. _V' % CO('N'))
w.qed([c, d, cx], 'fvmpt', '( N e. NN0 -> %s = %s )' % (EG('N'), CO('N'))); run(w)

# ---- encnatgamcl, encnatgamf, encnatgamlen, encnatgamfv
w = W('encnatgamcl', "Closure of encNatGam: a word over Gamma'.")
A = 'N e. NN0'
v = w.s([], 'encnatgamval', '( %s -> %s = %s )' % (A, EG('N'), CO('N')))
e = w.s([], 'encnatcl', '( %s -> %s e. Word 2o )' % (A, ENC('N')))
f = w.s([], 'inclboolf', "inclBool : 2o --> Gamma'"); fd = w.s([f], 'a1i', "( %s -> inclBool : 2o --> Gamma' )" % A)
wi = w.inst('wrdco'); c = w.s([e, fd, wi], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (A, CO('N')))
w.qed([v, c], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (A, EG('N'))); run(w)

w = W('encnatgamf', "encNatGam is a function from the natural numbers to the words over Gamma'.")
d = w.s([], 'df-encnatgam', 'encNatGam = ( n e. NN0 |-> %s )' % CO('n'))
e = w.s([], 'encnatcl', '( n e. NN0 -> %s e. Word 2o )' % ENC('n'))
f = w.s([], 'inclboolf', "inclBool : 2o --> Gamma'"); fd = w.s([f], 'a1i', "( n e. NN0 -> inclBool : 2o --> Gamma' )")
wi = w.inst('wrdco'); c = w.s([e, fd, wi], 'syl2anc', "( n e. NN0 -> %s e. Word Gamma' )" % CO('n'))
w.qed([d, c], 'fmpti', "encNatGam : NN0 --> Word Gamma'"); run(w)

w = W('encnatgamlen', 'The length of encNatGam N is the length of encodeNat N.')
A = 'N e. NN0'
v = w.s([], 'encnatgamval', '( %s -> %s = %s )' % (A, EG('N'), CO('N')))
vh = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, EG('N'), CO('N')))
e = w.s([], 'encnatcl', '( %s -> %s e. Word 2o )' % (A, ENC('N')))
f = w.s([], 'inclboolf', "inclBool : 2o --> Gamma'"); fd = w.s([f], 'a1i', "( %s -> inclBool : 2o --> Gamma' )" % A)
li = w.inst('lenco'); l = w.s([e, fd, li], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (A, CO('N'), LEN('N')))
w.qed([vh, l], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (A, EG('N'), LEN('N'))); run(w)

w = W('encnatgamfv', 'The I-th letter of encNatGam N is the I-th digit of N as a bit letter.')
A = '( N e. NN0 /\\ I e. ( 0 ..^ %s ) )' % LEN('N')
n = w.s([], 'simpl', '( %s -> N e. NN0 )' % A); ii = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ %s ) )' % (A, LEN('N')))
vi = w.inst('encnatgamval'); v = w.s([n, vi], 'syl', '( %s -> %s = %s )' % (A, EG('N'), CO('N')))
v1 = w.s([v], 'fveq1d', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (A, EG('N'), CO('N')))
ei = w.inst('encnatcl'); e = w.s([n, ei], 'syl', '( %s -> %s e. Word 2o )' % (A, ENC('N')))
wf = w.inst('wrdf'); ef = w.s([e, wf], 'syl', '( %s -> %s : ( 0 ..^ %s ) --> 2o )' % (A, ENC('N'), LEN('N')))
co = w.inst('fvco3'); c = w.s([ef, ii, co], 'syl2anc', '( %s -> ( %s ` I ) = ( inclBool ` ( %s ` I ) ) )' % (A, CO('N'), ENC('N')))
fe = w.inst('ffvelcdm'); b = w.s([ef, ii, fe], 'syl2anc', '( %s -> ( %s ` I ) e. 2o )' % (A, ENC('N')))
bi = w.inst('inclboolfv'); bv = w.s([b, bi], 'syl', '( %s -> ( inclBool ` ( %s ` I ) ) = <. 1 , ( %s ` I ) >. )' % (A, ENC('N'), ENC('N')))
c2 = w.s([c, bv], 'eqtrd', '( %s -> ( %s ` I ) = <. 1 , ( %s ` I ) >. )' % (A, CO('N'), ENC('N')))
w.qed([v1, c2], 'eqtrd', '( %s -> ( %s ` I ) = <. 1 , ( %s ` I ) >. )' % (A, EG('N'), ENC('N'))); run(w)
