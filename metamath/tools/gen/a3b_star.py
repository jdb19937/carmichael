"""Sortie A3b, batch 2: the pointwise chain of Lean's star_boundW at windowed
scales (A3b-blueprint.md section 2.2)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
import a3blib as LIB
from a3blib import HC, HC1, HC2, HN, NS, N5, IW, P2, A, B
from tm import *
from lin import linarith
import num
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

a, b = A(), B()
n = NS()
ANT = '( %s /\\ %s /\\ %s )' % (HC, HN(), IW())
ZB = '( 1 < Z /\\ %s <_ ( log ` Z ) /\\ ( log ` Z ) <_ ( 3 x. %s ) )' % (b, b)

def head(w):
    """the three top conjuncts of ANT and every basic fact"""
    hc = w.s([], 'simp1', '( %s -> %s )' % (ANT, HC))
    hn = w.s([], 'simp2', '( %s -> %s )' % (ANT, HN()))
    iw = w.s([], 'simp3', '( %s -> %s )' % (ANT, IW()))
    return LIB.basefacts(w, ANT, hc, hn, iw)

def st(w, hyps, ref, f):
    return w.s(hyps, ref, '( %s -> %s )' % (ANT, f))

# ------------------------------------------------------------------ extrwzcw
w = W('extrwzcw', 'The z bounds at windowed scales: 1 < z and ell3 n <_ log z <_ 3 ell3 n (Lean: the z-bounds block of star_boundW of ExtractionW.lean).')
d = head(w)
p1 = st(w, [d['hc1'], st(w, [d['are'], d['bre'], d['beq']], '3jca', '( %s e. RR /\\ %s e. RR /\\ %s = ( log ` %s ) )' % (a, b, b, a))], 'jca',
        '( %s /\\ ( %s e. RR /\\ %s e. RR /\\ %s = ( log ` %s ) ) )' % (HC1, a, b, b, a))
p2 = st(w, [st(w, [d['n2'], d['n3'], d['n4']], '3jca', '( %s /\\ %s /\\ %s )' % (n[1], n[2], n[3])),
            st(w, [d['zn0'], d['zlo'], d['zhi']], '3jca', '( Z e. NN0 /\\ ( ( C x. %s ) x. %s ) <_ Z /\\ Z <_ ( 4 x. ( ( C x. %s ) x. %s ) ) )' % (a, b, a, b))], 'jca',
        '( ( %s /\\ %s /\\ %s ) /\\ ( Z e. NN0 /\\ ( ( C x. %s ) x. %s ) <_ Z /\\ Z <_ ( 4 x. ( ( C x. %s ) x. %s ) ) ) )' % (n[1], n[2], n[3], a, b, a, b))
w.qed([p1, p2, w.inst('extrwzb')], 'syl2anc', '( %s -> %s )' % (ANT, ZB))
assert run(w)

# ------------------------------------------------------------------ extrwkyw
w = W('extrwkyw', 'The key bound at windowed scales: ( y + 1 ) log z <_ ell2 n / 100 (Lean: hkey of star_boundW of ExtractionW.lean).')
d = head(w)
zb = st(w, [], 'extrwzcw', ZB)
z1lt = st(w, [zb], 'simp1d', '1 < Z')
z1 = st(w, [z1lt], 'ltled', '1 <_ Z')
lzub = st(w, [zb], 'simp3d', '( log ` Z ) <_ ( 3 x. %s )' % b)
z0 = linarith(w, ANT, [z1lt], '0 < Z', leaves={'Z': ('RR', d['zre'])})
# extrwz1e
q1 = st(w, [d['hc1'], d['hc2']], 'jca', HC)
q2 = st(w, [d['arb'], d['br1']], 'jca', '( ( %s e. RR /\\ ; 5 0 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s ) )' % (a, a, b, b))
q3 = st(w, [d['zn0'], d['zhi'], z0], '3jca', '( Z e. NN0 /\\ Z <_ ( 4 x. ( ( C x. %s ) x. %s ) ) /\\ 0 < Z )' % (a, b))
z1e = st(w, [q1, q2, q3, w.inst('extrwz1e')], 'syl3anc', '( Z ^c ( 1 - %s ) ) <_ ( ( 4 x. C ) x. ( ( %s ^c ( 1 - E ) ) x. %s ) )'.replace('1 - %s', '1 - E') % (a, b))
# reassociate ( 4 x. C ) x. X  ->  4 x. ( C x. X )
X = '( ( %s ^c ( 1 - E ) ) x. %s )' % (a, b)
i4cn = st(w, [num.cc(w, '4')], 'a1i', '4 e. CC')
ccn = st(w, [d['cre']], 'recnd', 'C e. CC')
ere = d['ere']
e1re = st(w, [w.s([], '1red', '( %s -> 1 e. RR )' % ANT), ere], 'resubcld', '( 1 - E ) e. RR')
age0 = linarith(w, ANT, [d['n2']], '0 <_ %s' % a, leaves={a: ('RR', d['are'])})
acxp = st(w, [d['are'], age0, e1re], 'recxpcld', '( %s ^c ( 1 - E ) ) e. RR' % a)
xre = st(w, [acxp, d['bre']], 'remulcld', '%s e. RR' % X)
xcn = st(w, [xre], 'recnd', '%s e. CC' % X)
ass = st(w, [i4cn, ccn, xcn], 'mulassd', '( ( 4 x. C ) x. %s ) = ( 4 x. ( C x. %s ) )' % (X, X))
z1e2 = st(w, [z1e, ass], 'breqtrd', '( Z ^c ( 1 - E ) ) <_ ( 4 x. ( C x. %s ) )' % X)
# extrwt1
T1 = '( ( ; 4 8 x. C ) x. ( ( %s ^c ( 1 - E ) ) x. ( %s ^ 2 ) ) ) <_ ( ( 1 / ; ; 2 0 0 ) x. %s )' % (a, b, a)
t1a = st(w, [d['hc1'], d['arb'], d['br1']], '3jca', '( %s /\\ ( %s e. RR /\\ ; 5 0 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s ) )' % (HC1, a, a, b, b))
t1b = st(w, [d['hc2'], st(w, [d['n5'], d['n6']], 'jca', '( %s /\\ %s )' % (N5(), n[5]))], 'jca',
         '( %s /\\ ( %s /\\ %s ) )' % (HC2, N5(), n[5]))
t1 = st(w, [t1a, t1b, w.inst('extrwt1')], 'syl2anc', T1)
# extrwt2
T2 = '( 3 x. %s ) <_ ( ( 1 / ; ; 2 0 0 ) x. %s )' % (b, a)
t2a = st(w, [d['arb'], d['br1'], d['hc2']], '3jca', '( ( %s e. RR /\\ ; 5 0 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s ) /\\ %s )' % (a, a, b, b, HC2))
t2b = st(w, [d['n5'], d['n7']], 'jca', '( %s /\\ %s )' % (N5(), n[6]))
t2 = st(w, [t2a, t2b, w.inst('extrwt2')], 'syl2anc', T2)
# extrwkey
k1 = st(w, [d['arb'], d['br1'], d['hc1']], '3jca', '( ( %s e. RR /\\ ; 5 0 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s ) /\\ %s )' % (a, a, b, b, HC1))
k2 = st(w, [d['hc2'], st(w, [d['yn0'], d['zn0'], z1], '3jca', '( Y e. NN0 /\\ Z e. NN0 /\\ 1 <_ Z )')], 'jca',
        '( %s /\\ ( Y e. NN0 /\\ Z e. NN0 /\\ 1 <_ Z ) )' % HC2)
k3 = st(w, [st(w, [z1e2, d['yhi']], 'jca', '( ( Z ^c ( 1 - E ) ) <_ ( 4 x. ( C x. %s ) ) /\\ Y <_ ( 4 x. ( Z ^c ( 1 - E ) ) ) )' % X),
            lzub, st(w, [t1, t2], 'jca', '( %s /\\ %s )' % (T1, T2))], '3jca',
        '( ( ( Z ^c ( 1 - E ) ) <_ ( 4 x. ( C x. %s ) ) /\\ Y <_ ( 4 x. ( Z ^c ( 1 - E ) ) ) ) /\\ ( log ` Z ) <_ ( 3 x. %s ) /\\ ( %s /\\ %s ) )' % (X, b, T1, T2))
w.qed([k1, k2, k3, w.inst('extrwkey')], 'syl3anc', '( %s -> ( ( Y + 1 ) x. ( log ` Z ) ) <_ ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % (ANT, a))
assert run(w)

# ------------------------------------------------------------------ extrwp2w
w = W('extrwp2w', 'The second factor of the budget at windowed scales: z ^ ( y + 1 ) ( 1 + T log z ) + 2 <_ exp ( ell2 n / 10 ) (Lean: hP2 of star_boundW of ExtractionW.lean).')
d = head(w)
zb = st(w, [], 'extrwzcw', ZB)
z1 = st(w, [st(w, [zb], 'simp1d', '1 < Z')], 'ltled', '1 <_ Z')
lzub = st(w, [zb], 'simp3d', '( log ` Z ) <_ ( 3 x. %s )' % b)
key = st(w, [], 'extrwkyw', '( ( Y + 1 ) x. ( log ` Z ) ) <_ ( ( 1 / ; ; 1 0 0 ) x. %s )' % a)
a1 = linarith(w, ANT, [d['n2']], '1 <_ %s' % a, leaves={a: ('RR', d['are'])})
lgle = st(w, [d['are'], a1, w.inst('loglet')], 'syl2anc', '( log ` %s ) <_ %s' % (a, a))
bla = st(w, [d['beq'], lgle], 'eqbrtrd', '%s <_ %s' % (b, a))
p1 = st(w, [d['arb'],
            st(w, [d['bre'], d['n3'], bla], '3jca', '( %s e. RR /\\ 1 <_ %s /\\ %s <_ %s )' % (b, b, b, a)),
            st(w, [d['tn0'], d['thi']], 'jca', '( T e. NN0 /\\ T <_ ( 5 x. %s ) )' % a)], '3jca',
        '( ( %s e. RR /\\ ; 5 0 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s /\\ %s <_ %s ) /\\ ( T e. NN0 /\\ T <_ ( 5 x. %s ) ) )' % (a, a, b, b, b, a, a))
p2 = st(w, [st(w, [d['yn0'], d['zn0'], z1], '3jca', '( Y e. NN0 /\\ Z e. NN0 /\\ 1 <_ Z )'),
            st(w, [lzub, key], 'jca', '( ( log ` Z ) <_ ( 3 x. %s ) /\\ ( ( Y + 1 ) x. ( log ` Z ) ) <_ ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % (b, a)),
            d['n8']], '3jca',
        '( ( Y e. NN0 /\\ Z e. NN0 /\\ 1 <_ Z ) /\\ ( ( log ` Z ) <_ ( 3 x. %s ) /\\ ( ( Y + 1 ) x. ( log ` Z ) ) <_ ( ( 1 / ; ; 1 0 0 ) x. %s ) ) /\\ %s )' % (b, a, n[7]))
w.qed([p1, p2, w.inst('extrwp2')], 'syl2anc', '( %s -> %s <_ ( exp ` ( ( 1 / ; 1 0 ) x. %s ) ) )' % (ANT, P2, a))
assert run(w)
