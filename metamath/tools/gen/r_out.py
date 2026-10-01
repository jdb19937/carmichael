"""Sortie S, batch 3: encodeOutput (value, closure, the equation lemmas for nil and snoc) via the free monoid on Gamma'."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

PF = '( p e. NN0 |-> ( ( encNatGam ` p ) ++ <" 4 "> ) )'
FM = "( freeMnd ` Gamma' )"
WG = "Word Gamma'"; WWG = "Word Word Gamma'"
C4 = '<" 4 ">'
EG = lambda N: '( encNatGam ` %s )' % N
EG4 = lambda N: '( ( encNatGam ` %s ) ++ <" 4 "> )' % N
FLAT = lambda S: '( %s gsum ( %s o. %s ) )' % (FM, PF, S)
BODY = lambda M, S: '( %s ++ ( <" 4 "> ++ %s ) )' % (EG(M), FLAT(S))
OUT = lambda M, S: '( %s encodeOutput %s )' % (M, S)

# ---- the free monoid on Gamma'
w = W('frmdgam', "The free monoid on Gamma' is a monoid.")
e = w.s([], 'eqid', '%s = %s' % (FM, FM)); m = w.s([e], 'frmdmnd', "( Gamma' e. _V -> %s e. Mnd )" % FM); g = w.s([], 'gammaex', "Gamma' e. _V")
w.qed([g, m], 'ax-mp', '%s e. Mnd' % FM); run(w)

w = W('frmdgambas', "The base set of the free monoid on Gamma' is the set of words over Gamma'.")
e = w.s([], 'eqid', '%s = %s' % (FM, FM)); e2 = w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (FM, FM))
b = w.s([e, e2], 'frmdbas', "( Gamma' e. _V -> ( Base ` %s ) = %s )" % (FM, WG)); g = w.s([], 'gammaex', "Gamma' e. _V")
w.qed([g, b], 'ax-mp', '( Base ` %s ) = %s' % (FM, WG)); run(w)

w = W('frmdgam0', "The identity of the free monoid on Gamma' is the empty word.")
e = w.s([], 'eqid', '%s = %s' % (FM, FM)); z = w.s([e], 'frmd0', '(/) = ( 0g ` %s )' % FM)
w.qed([z], 'eqcomi', '( 0g ` %s ) = (/)' % FM); run(w)

w = W('frmdgamadd', "The operation of the free monoid on Gamma' is concatenation.")
e = w.s([], 'eqid', '%s = %s' % (FM, FM)); b = w.s([], 'frmdgambas', '( Base ` %s ) = %s' % (FM, WG)); b2 = w.s([b], 'eqcomi', '%s = ( Base ` %s )' % (WG, FM))
p = w.s([], 'eqid', '( +g ` %s ) = ( +g ` %s )' % (FM, FM))
w.qed([e, b2, p], 'frmdadd', '( ( X e. %s /\\ Y e. %s ) -> ( X ( +g ` %s ) Y ) = ( X ++ Y ) )' % (WG, WG, FM)); run(w)

w = W('gsumgamcl', "The monoid sum of a word of words over Gamma' is a word over Gamma'.")
b = w.s([], 'frmdgambas', '( Base ` %s ) = %s' % (FM, WG)); b2 = w.s([b], 'eqcomi', '%s = ( Base ` %s )' % (WG, FM))
m = w.s([], 'frmdgam', '%s e. Mnd' % FM)
c = w.s([b2], 'gsumwcl', '( ( %s e. Mnd /\\ W e. %s ) -> ( %s gsum W ) e. %s )' % (FM, WWG, FM, WG))
w.qed([m, c], 'mpan', '( W e. %s -> ( %s gsum W ) e. %s )' % (WWG, FM, WG)); run(w)

w = W('gsumgamccat', "The monoid sum of a concatenation of words of words over Gamma' is the concatenation of the sums.")
A = '( W e. %s /\\ X e. %s )' % (WWG, WWG)
b = w.s([], 'frmdgambas', '( Base ` %s ) = %s' % (FM, WG)); b2 = w.s([b], 'eqcomi', '%s = ( Base ` %s )' % (WG, FM))
p = w.s([], 'eqid', '( +g ` %s ) = ( +g ` %s )' % (FM, FM))
m = w.s([], 'frmdgam', '%s e. Mnd' % FM)
c = w.s([b2, p], 'gsumccat', '( ( %s e. Mnd /\\ W e. %s /\\ X e. %s ) -> ( %s gsum ( W ++ X ) ) = ( ( %s gsum W ) ( +g ` %s ) ( %s gsum X ) ) )' % (FM, WWG, WWG, FM, FM, FM, FM))
c2 = w.s([m, c], 'mp3an1', '( %s -> ( %s gsum ( W ++ X ) ) = ( ( %s gsum W ) ( +g ` %s ) ( %s gsum X ) ) )' % (A, FM, FM, FM, FM))
w1 = w.s([], 'simpl', '( %s -> W e. %s )' % (A, WWG)); x1 = w.s([], 'simpr', '( %s -> X e. %s )' % (A, WWG))
ci = w.inst('gsumgamcl'); cw = w.s([w1, ci], 'syl', '( %s -> ( %s gsum W ) e. %s )' % (A, FM, WG)); cx = w.s([x1, w.inst('gsumgamcl')], 'syl', '( %s -> ( %s gsum X ) e. %s )' % (A, FM, WG))
ai = w.inst('frmdgamadd'); a = w.s([cw, cx, ai], 'syl2anc', '( %s -> ( ( %s gsum W ) ( +g ` %s ) ( %s gsum X ) ) = ( ( %s gsum W ) ++ ( %s gsum X ) ) )' % (A, FM, FM, FM, FM, FM))
w.qed([c2, a], 'eqtrd', '( %s -> ( %s gsum ( W ++ X ) ) = ( ( %s gsum W ) ++ ( %s gsum X ) ) )' % (A, FM, FM, FM)); run(w)

w = W('gsumgams1', "The monoid sum of a one-letter word of words over Gamma' is the letter.")
b = w.s([], 'frmdgambas', '( Base ` %s ) = %s' % (FM, WG)); b2 = w.s([b], 'eqcomi', '%s = ( Base ` %s )' % (WG, FM))
w.qed([b2], 'gsumws1', '( S e. %s -> ( %s gsum <" S "> ) = S )' % (WG, FM)); run(w)

w = W('gsumgam0', "The monoid sum of the empty word of words over Gamma' is the empty word.")
e = w.s([], 'eqid', '%s = %s' % (FM, FM)); z = w.s([e], 'frmd0', '(/) = ( 0g ` %s )' % FM)
w.qed([z], 'gsum0', '( %s gsum (/) ) = (/)' % FM); run(w)

# ---- the mapped word and its sum
w = W('encoutpf', "The letter-and-comma mapping of encodeOutput is a function from the natural numbers to the words over Gamma'.")
e = w.s([], 'eqid', '%s = %s' % (PF, PF))
c = w.s([], 'encnatgamcl', '( p e. NN0 -> %s e. %s )' % (EG('p'), WG))
g = w.s([], 'gamma4', "4 e. Gamma'"); gd = w.s([g], 'a1i', "( p e. NN0 -> 4 e. Gamma' )")
ci = w.inst('ccatws1cl'); cc = w.s([c, gd, ci], 'syl2anc', '( p e. NN0 -> %s e. %s )' % (EG4('p'), WG))
w.qed([e, cc], 'fmpti', '%s : NN0 --> %s' % (PF, WG)); run(w)

w = W('encoutpfv', 'Value of the letter-and-comma mapping of encodeOutput.')
c1 = w.s([], 'fveq2', '( p = P -> %s = %s )' % (EG('p'), EG('P'))); c = w.s([c1], 'oveq1d', '( p = P -> %s = %s )' % (EG4('p'), EG4('P')))
e = w.s([], 'eqid', '%s = %s' % (PF, PF)); x = w.s([], 'ovex', '%s e. _V' % EG4('P'))
w.qed([c, e, x], 'fvmpt', '( P e. NN0 -> ( %s ` P ) = %s )' % (PF, EG4('P'))); run(w)

w = W('encoutflatcl', "The encoded list part of encodeOutput is a word over Gamma'.")
A = 'S e. Word NN0'
f = w.s([], 'encoutpf', '%s : NN0 --> %s' % (PF, WG)); fd = w.s([f], 'a1i', '( %s -> %s : NN0 --> %s )' % (A, PF, WG))
i = w.s([], 'id', '( %s -> S e. Word NN0 )' % A)
wi = w.inst('wrdco'); c = w.s([i, fd, wi], 'syl2anc', '( %s -> ( %s o. S ) e. %s )' % (A, PF, WWG))
gi = w.inst('gsumgamcl'); w.qed([c, gi], 'syl', '( %s -> %s e. %s )' % (A, FLAT('S'), WG)); run(w)

w = W('encoutflat0', 'The encoded list part of encodeOutput for the empty list is the empty word.')
c = w.s([], 'co02', '( %s o. (/) ) = (/)' % PF); o = w.s([c], 'oveq2i', '%s = ( %s gsum (/) )' % (FLAT('(/)'), FM))
z = w.s([], 'gsumgam0', '( %s gsum (/) ) = (/)' % FM)
w.qed([o, z], 'eqtri', '%s = (/)' % FLAT('(/)')); run(w)

w = W('encoutflatccat', 'The encoded list part of encodeOutput for a concatenation of lists is the concatenation of the parts.')
A = '( S e. Word NN0 /\\ T e. Word NN0 )'
s1 = w.s([], 'simpl', '( %s -> S e. Word NN0 )' % A); t1 = w.s([], 'simpr', '( %s -> T e. Word NN0 )' % A)
f = w.s([], 'encoutpf', '%s : NN0 --> %s' % (PF, WG)); fd = w.s([f], 'a1i', '( %s -> %s : NN0 --> %s )' % (A, PF, WG))
ci = w.inst('ccatco'); c = w.s([s1, t1, fd, ci], 'syl3anc', '( %s -> ( %s o. ( S ++ T ) ) = ( ( %s o. S ) ++ ( %s o. T ) ) )' % (A, PF, PF, PF))
o = w.s([c], 'oveq2d', '( %s -> %s = ( %s gsum ( ( %s o. S ) ++ ( %s o. T ) ) ) )' % (A, FLAT('( S ++ T )'), FM, PF, PF))
wi = w.inst('wrdco'); cs = w.s([s1, fd, wi], 'syl2anc', '( %s -> ( %s o. S ) e. %s )' % (A, PF, WWG)); ct = w.s([t1, fd, w.inst('wrdco')], 'syl2anc', '( %s -> ( %s o. T ) e. %s )' % (A, PF, WWG))
gi = w.inst('gsumgamccat'); g = w.s([cs, ct, gi], 'syl2anc', '( %s -> ( %s gsum ( ( %s o. S ) ++ ( %s o. T ) ) ) = ( %s ++ %s ) )' % (A, FM, PF, PF, FLAT('S'), FLAT('T')))
w.qed([o, g], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (A, FLAT('( S ++ T )'), FLAT('S'), FLAT('T'))); run(w)

w = W('encoutflats1', 'The encoded list part of encodeOutput for a one-element list.')
A = 'P e. NN0'
i = w.s([], 'id', '( %s -> P e. NN0 )' % A)
f = w.s([], 'encoutpf', '%s : NN0 --> %s' % (PF, WG)); fd = w.s([f], 'a1i', '( %s -> %s : NN0 --> %s )' % (A, PF, WG))
si = w.inst('s1co'); c = w.s([i, fd, si], 'syl2anc', '( %s -> ( %s o. <" P "> ) = <" ( %s ` P ) "> )' % (A, PF, PF))
o = w.s([c], 'oveq2d', '( %s -> %s = ( %s gsum <" ( %s ` P ) "> ) )' % (A, FLAT('<" P ">'), FM, PF))
fe = w.inst('ffvelcdm'); v = w.s([fd, i, fe], 'syl2anc', '( %s -> ( %s ` P ) e. %s )' % (A, PF, WG))
gi = w.inst('gsumgams1'); g = w.s([v, gi], 'syl', '( %s -> ( %s gsum <" ( %s ` P ) "> ) = ( %s ` P ) )' % (A, FM, PF, PF))
pv = w.s([], 'encoutpfv', '( %s -> ( %s ` P ) = %s )' % (A, PF, EG4('P')))
g2 = w.s([g, pv], 'eqtrd', '( %s -> ( %s gsum <" ( %s ` P ) "> ) = %s )' % (A, FM, PF, EG4('P')))
w.qed([o, g2], 'eqtrd', '( %s -> %s = %s )' % (A, FLAT('<" P ">'), EG4('P'))); run(w)

# ---- encodeOutput itself
w = W('encoutval', 'Value of encodeOutput on a number M and a list S of numbers.')
A = '( m = M /\\ s = S )'
l1 = w.s([], 'simpl', '( %s -> m = M )' % A); l2 = w.s([], 'simpr', '( %s -> s = S )' % A)
c, b = w.congr(BODY('m', 's'), {'m': 'M', 's': 'S'}, A, {'m': l1, 's': l2}); assert b == BODY('M', 'S'), b
d = w.s([], 'df-encout', 'encodeOutput = ( m e. NN0 , s e. Word NN0 |-> %s )' % BODY('m', 's'))
x = w.s([], 'ovex', '%s e. _V' % BODY('M', 'S'))
w.qed([c, d, x], 'ovmpoa', '( ( M e. NN0 /\\ S e. Word NN0 ) -> %s = %s )' % (OUT('M', 'S'), BODY('M', 'S'))); run(w)

w = W('encoutcl', "Closure of encodeOutput: a word over Gamma'.")
A = '( M e. NN0 /\\ S e. Word NN0 )'
m1 = w.s([], 'simpl', '( %s -> M e. NN0 )' % A); s1 = w.s([], 'simpr', '( %s -> S e. Word NN0 )' % A)
v = w.s([], 'encoutval', '( %s -> %s = %s )' % (A, OUT('M', 'S'), BODY('M', 'S')))
ei = w.inst('encnatgamcl'); e = w.s([m1, ei], 'syl', '( %s -> %s e. %s )' % (A, EG('M'), WG))
g = w.s([], 'gamma4', "4 e. Gamma'"); gs = w.s([g, w.inst('s1cl')], 'ax-mp', '%s e. %s' % (C4, WG)); gsd = w.s([gs], 'a1i', '( %s -> %s e. %s )' % (A, C4, WG))
fi = w.inst('encoutflatcl'); f = w.s([s1, fi], 'syl', '( %s -> %s e. %s )' % (A, FLAT('S'), WG))
ci = w.inst('ccatcl'); c1 = w.s([gsd, f, ci], 'syl2anc', '( %s -> ( %s ++ %s ) e. %s )' % (A, C4, FLAT('S'), WG))
c2 = w.s([e, c1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. %s )' % (A, BODY('M', 'S'), WG))
w.qed([v, c2], 'eqeltrd', '( %s -> %s e. %s )' % (A, OUT('M', 'S'), WG)); run(w)

w = W('encoutf', "encodeOutput is a function from pairs (number, list of numbers) to the words over Gamma'.")
A = '( m e. NN0 /\\ s e. Word NN0 )'
v = w.s([], 'encoutval', '( %s -> %s = %s )' % (A, OUT('m', 's'), BODY('m', 's')))
c = w.s([], 'encoutcl', '( %s -> %s e. %s )' % (A, OUT('m', 's'), WG))
b = w.s([v, c], 'eqeltrrd', '( %s -> %s e. %s )' % (A, BODY('m', 's'), WG))
r = w.s([b], 'rgen2', 'A. m e. NN0 A. s e. Word NN0 %s e. %s' % (BODY('m', 's'), WG))
d = w.s([], 'df-encout', 'encodeOutput = ( m e. NN0 , s e. Word NN0 |-> %s )' % BODY('m', 's'))
f = w.s([d], 'fmpo', '( A. m e. NN0 A. s e. Word NN0 %s e. %s <-> encodeOutput : ( NN0 X. Word NN0 ) --> %s )' % (BODY('m', 's'), WG, WG))
w.qed([r, f], 'mpbi', 'encodeOutput : ( NN0 X. Word NN0 ) --> %s' % WG); run(w)

w = W('encoutfv', 'encodeOutput applied to an ordered pair is the operation value (the form TM2CompT uses).')
d = w.s([], 'df-ov', '%s = ( encodeOutput ` <. M , S >. )' % OUT('M', 'S'))
w.qed([d], 'eqcomi', '( encodeOutput ` <. M , S >. ) = %s' % OUT('M', 'S')); run(w)

w = W('encoutnil', 'encodeOutput of a number and the empty list: the number followed by a comma (Lean: encodeOutput (m, []) ).')
A = 'M e. NN0'
z = w.s([], 'wrd0', '(/) e. Word NN0'); vi = w.inst('encoutval'); v = w.s([z, vi], 'mpan2', '( %s -> %s = %s )' % (A, OUT('M', '(/)'), BODY('M', '(/)')))
f0 = w.s([], 'encoutflat0', '%s = (/)' % FLAT('(/)')); o = w.s([f0], 'oveq2i', '( %s ++ %s ) = ( %s ++ (/) )' % (C4, FLAT('(/)'), C4))
g = w.s([], 'gamma4', "4 e. Gamma'"); gs = w.s([g, w.inst('s1cl')], 'ax-mp', '%s e. %s' % (C4, WG)); ri = w.inst('ccatrid'); r = w.s([gs, ri], 'ax-mp', '( %s ++ (/) ) = %s' % (C4, C4))
o2 = w.s([o, r], 'eqtri', '( %s ++ %s ) = %s' % (C4, FLAT('(/)'), C4)); o3 = w.s([o2], 'oveq2i', '%s = ( %s ++ %s )' % (BODY('M', '(/)'), EG('M'), C4))
o3d = w.s([o3], 'a1i', '( %s -> %s = ( %s ++ %s ) )' % (A, BODY('M', '(/)'), EG('M'), C4))
w.qed([v, o3d], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (A, OUT('M', '(/)'), EG('M'), C4)); run(w)

w = W('encouts1', 'encodeOutput of a list extended by one number: the previous encoding followed by the number and a comma.')
A = '( M e. NN0 /\\ S e. Word NN0 /\\ P e. NN0 )'
m1 = w.s([], 'simp1', '( %s -> M e. NN0 )' % A); s1 = w.s([], 'simp2', '( %s -> S e. Word NN0 )' % A); p1 = w.s([], 'simp3', '( %s -> P e. NN0 )' % A)
SP = '( S ++ <" P "> )'
si = w.inst('ccatws1cl'); sp = w.s([s1, p1, si], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A, SP))
vi = w.inst('encoutval'); v = w.s([m1, sp, vi], 'syl2anc', '( %s -> %s = %s )' % (A, OUT('M', SP), BODY('M', SP)))
ps = w.s([p1], 's1cld', '( %s -> <" P "> e. Word NN0 )' % A)
fci = w.inst('encoutflatccat'); fc = w.s([s1, ps, fci], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (A, FLAT(SP), FLAT('S'), FLAT('<" P ">')))
fsi = w.inst('encoutflats1'); fs = w.s([p1, fsi], 'syl', '( %s -> %s = %s )' % (A, FLAT('<" P ">'), EG4('P')))
fs2 = w.s([fs], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (A, FLAT('S'), FLAT('<" P ">'), FLAT('S'), EG4('P')))
fc2 = w.s([fc, fs2], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (A, FLAT(SP), FLAT('S'), EG4('P')))
fc3 = w.s([fc2], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (A, C4, FLAT(SP), C4, FLAT('S'), EG4('P')))
# closures for ccatass
g = w.s([], 'gamma4', "4 e. Gamma'"); gs = w.s([g, w.inst('s1cl')], 'ax-mp', '%s e. %s' % (C4, WG)); gsd = w.s([gs], 'a1i', '( %s -> %s e. %s )' % (A, C4, WG))
fl = w.s([s1, w.inst('encoutflatcl')], 'syl', '( %s -> %s e. %s )' % (A, FLAT('S'), WG))
ep = w.s([p1, w.inst('encnatgamcl')], 'syl', '( %s -> %s e. %s )' % (A, EG('P'), WG))
g4d = w.s([g], 'a1i', "( %s -> 4 e. Gamma' )" % A); ep4 = w.s([ep, g4d, w.inst('ccatws1cl')], 'syl2anc', '( %s -> %s e. %s )' % (A, EG4('P'), WG))
as1 = w.s([gsd, fl, ep4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (A, C4, FLAT('S'), EG4('P'), C4, FLAT('S'), EG4('P')))
fc4 = w.s([fc3, as1], 'eqtr4d', '( %s -> ( %s ++ %s ) = ( ( %s ++ %s ) ++ %s ) )' % (A, C4, FLAT(SP), C4, FLAT('S'), EG4('P')))
fc5 = w.s([fc4], 'oveq2d', '( %s -> %s = ( %s ++ ( ( %s ++ %s ) ++ %s ) ) )' % (A, BODY('M', SP), EG('M'), C4, FLAT('S'), EG4('P')))
em = w.s([m1, w.inst('encnatgamcl')], 'syl', '( %s -> %s e. %s )' % (A, EG('M'), WG))
c4f = w.s([gsd, fl, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. %s )' % (A, C4, FLAT('S'), WG))
as2 = w.s([em, c4f, ep4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( %s ++ %s ) ) ++ %s ) = ( %s ++ ( ( %s ++ %s ) ++ %s ) ) )' % (A, EG('M'), C4, FLAT('S'), EG4('P'), EG('M'), C4, FLAT('S'), EG4('P')))
fc6 = w.s([fc5, as2], 'eqtr4d', '( %s -> %s = ( %s ++ %s ) )' % (A, BODY('M', SP), BODY('M', 'S'), EG4('P')))
vs = w.s([m1, s1, w.inst('encoutval')], 'syl2anc', '( %s -> %s = %s )' % (A, OUT('M', 'S'), BODY('M', 'S')))
vs2 = w.s([vs], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (A, OUT('M', 'S'), EG4('P'), BODY('M', 'S'), EG4('P')))
fc7 = w.s([fc6, vs2], 'eqtr4d', '( %s -> %s = ( %s ++ %s ) )' % (A, BODY('M', SP), OUT('M', 'S'), EG4('P')))
w.qed([v, fc7], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (A, OUT('M', SP), OUT('M', 'S'), EG4('P'))); run(w)
