import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); Ly=LY(T); STK=STK_ = '( TM2Stk ` T )'; SAT=SA(T)
def LYn(n): return LYN(T, n)
def FN_(n): return FN(T, n)
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)
IXP = 'X_ k e. %s Word ( %s ` k )' % (Kt, Gt)
def WD(k): return 'Word ( %s ` %s )' % (Gt, k)

# ---- tm2layelim
w = W('tm2layelim', 'Inversion of the constructor layer: an element of ( T TM2lay X ) is in X or is one application of a constructor to elements of X.')
def elim(node):
    Kd = node.kind
    if Kd == 'atom':
        return None, 'Q e. %s' % node.text()
    if Kd == 'sn':
        return w.s([], 'elsni', '( Q e. %s -> Q = %s )' % (node.text(), node.kids[0].text())), 'Q = %s' % node.kids[0].text()
    if Kd == 'iun':
        v = node.bound[0]; A_, B_ = node.kids
        sub_, wb = elim(B_)
        e0 = w.s([], 'eliun', '( Q e. %s <-> E. %s e. %s Q e. %s )' % (node.text(), v, A_.text(), B_.text()))
        e1 = w.s([e0], 'biimpi', '( Q e. %s -> E. %s e. %s Q e. %s )' % (node.text(), v, A_.text(), B_.text()))
        if sub_ is None: return e1, 'E. %s e. %s Q e. %s' % (v, A_.text(), B_.text())
        r = w.s([sub_], 'reximi', '( E. %s e. %s Q e. %s -> E. %s e. %s %s )' % (v, A_.text(), B_.text(), v, A_.text(), wb))
        return w.s([e1, r], 'syl', '( Q e. %s -> E. %s e. %s %s )' % (node.text(), v, A_.text(), wb)), 'E. %s e. %s %s' % (v, A_.text(), wb)
    if Kd == 'in:u.':
        B_, C_ = node.kids
        s1, w1 = elim(B_); s2, w2 = elim(C_)
        if s1 is None: s1 = w.s([], 'id', '( Q e. %s -> Q e. %s )' % (B_.text(), B_.text()))
        if s2 is None: s2 = w.s([], 'id', '( Q e. %s -> Q e. %s )' % (C_.text(), C_.text()))
        e0 = w.s([], 'elun', '( Q e. %s <-> ( Q e. %s \\/ Q e. %s ) )' % (node.text(), B_.text(), C_.text()))
        e1 = w.s([e0], 'biimpi', '( Q e. %s -> ( Q e. %s \\/ Q e. %s ) )' % (node.text(), B_.text(), C_.text()))
        o = w.s([s1, s2], 'orim12i', '( ( Q e. %s \\/ Q e. %s ) -> ( %s \\/ %s ) )' % (B_.text(), C_.text(), w1, w2))
        return w.s([e1, o], 'syl', '( Q e. %s -> ( %s \\/ %s ) )' % (node.text(), w1, w2)), '( %s \\/ %s )' % (w1, w2)
    raise NotImplementedError(Kd)
st, WFF = elim(parse(PHI(T, 'X')))
B = '( T e. V /\\ X e. W )'
v = w.s([], 'tm2layval', '( %s -> ( T TM2lay X ) = %s )' % (B, PHI(T, 'X')))
v2 = w.s([v], 'eleq2d', '( %s -> ( Q e. ( T TM2lay X ) <-> Q e. %s ) )' % (B, PHI(T, 'X')))
w.qed([v2, st], 'biimtrdi', '( %s -> ( Q e. ( T TM2lay X ) -> %s ) )' % (B, WFF))
run(w)
open(os.path.join(ROOT, 'scratch', 'tm2layelim.wff'), 'w').write(WFF)

# ---- tm2stkfn
w = W('tm2stkfn', 'The stacks form a function on the stack indices.')
A = '( T e. V /\\ D e. %s )' % STK
a1 = w.s([], 'simpl', '( %s -> T e. V )' % A); a2 = w.s([], 'simpr', '( %s -> D e. %s )' % (A, STK))
v = w.inst('tm2stkval'); v2 = w.s([a1, v], 'syl', '( %s -> %s = %s )' % (A, STK, IXP))
d = w.s([a2, v2], 'eleqtrd', '( %s -> D e. %s )' % (A, IXP))
i = w.inst('ixpfn'); w.qed([d, i], 'syl', '( %s -> D Fn %s )' % (A, Kt))
run(w)

# ---- tm2stkfv
w = W('tm2stkfv', 'Each stack is a word over its alphabet.')
A = '( T e. V /\\ D e. %s /\\ K e. %s )' % (STK, Kt)
a1 = w.s([], 'simp1', '( %s -> T e. V )' % A); a2 = w.s([], 'simp2', '( %s -> D e. %s )' % (A, STK)); a3 = w.s([], 'simp3', '( %s -> K e. %s )' % (A, Kt))
v = w.inst('tm2stkval'); v2 = w.s([a1, v], 'syl', '( %s -> %s = %s )' % (A, STK, IXP))
d = w.s([a2, v2], 'eleqtrd', '( %s -> D e. %s )' % (A, IXP))
e = w.s([], 'elixp2', '( D e. %s <-> ( D e. _V /\\ D Fn %s /\\ A. k e. %s ( D ` k ) e. %s ) )' % (IXP, Kt, Kt, WD('k')))
d2 = w.s([d, e], 'sylib', '( %s -> ( D e. _V /\\ D Fn %s /\\ A. k e. %s ( D ` k ) e. %s ) )' % (A, Kt, Kt, WD('k')))
d3 = w.s([d2], 'simp3d', '( %s -> A. k e. %s ( D ` k ) e. %s )' % (A, Kt, WD('k')))
l = w.s([], 'id', '( k = K -> k = K )'); c, _ = w.wcongr('( D ` k ) e. %s' % WD('k'), {'k': 'K'}, 'k = K', {'k': l})
w.qed([c, d3, a3], 'rspcdva', '( %s -> ( D ` K ) e. %s )' % (A, WD('K')))
run(w)

# ---- tm2stkupd
UPD = '( ( D |` ( %s \\ { K } ) ) u. { <. K , X >. } )' % Kt
UPDP = '( { <. K , X >. } u. ( D |` ( %s \\ { K } ) ) )' % Kt
w = W('tm2stkupd', 'Updating one stack by a word over its alphabet yields stacks (Lean\'s Function.update).')
A = '( T e. V /\\ D e. %s /\\ ( K e. %s /\\ X e. %s ) )' % (STK, Kt, WD('K'))
a1 = w.s([], 'simp1', '( %s -> T e. V )' % A); a2 = w.s([], 'simp2', '( %s -> D e. %s )' % (A, STK))
a3 = w.s([], 'simp3l', '( %s -> K e. %s )' % (A, Kt)); a4 = w.s([], 'simp3r', '( %s -> X e. %s )' % (A, WD('K')))
v = w.inst('tm2stkval'); v2 = w.s([a1, v], 'syl', '( %s -> %s = %s )' % (A, STK, IXP))
f1i = w.inst('tm2stkfn'); f1 = w.s([a1, a2, f1i], 'syl2anc', '( %s -> D Fn %s )' % (A, Kt))
f2 = w.s([], 'difss', '( %s \\ { K } ) C_ %s' % (Kt, Kt)); f2b = w.s([f2], 'a1i', '( %s -> ( %s \\ { K } ) C_ %s )' % (A, Kt, Kt))
f3i = w.inst('fnssres'); f3 = w.s([f1, f2b, f3i], 'syl2anc', '( %s -> ( D |` ( %s \\ { K } ) ) Fn ( %s \\ { K } ) )' % (A, Kt, Kt))
k1 = w.s([a3], 'elexd', '( %s -> K e. _V )' % A); x1 = w.s([a4], 'elexd', '( %s -> X e. _V )' % A)
f5i = w.inst('fnsng'); f5 = w.s([k1, x1, f5i], 'syl2anc', '( %s -> { <. K , X >. } Fn { K } )' % A)
f6 = w.s([], 'disjdifr', '( ( %s \\ { K } ) i^i { K } ) = (/)' % Kt); f6b = w.s([f6], 'a1i', '( %s -> ( ( %s \\ { K } ) i^i { K } ) = (/) )' % (A, Kt))
f7i = w.inst('fnun'); f7 = w.s([f3, f5, f6b, f7i], 'syl21anc', '( %s -> %s Fn ( ( %s \\ { K } ) u. { K } ) )' % (A, UPD, Kt))
f8i = w.inst('difsnid'); f8 = w.s([a3, f8i], 'syl', '( %s -> ( ( %s \\ { K } ) u. { K } ) = %s )' % (A, Kt, Kt))
f9 = w.s([f8], 'fneq2d', '( %s -> ( %s Fn ( ( %s \\ { K } ) u. { K } ) <-> %s Fn %s ) )' % (A, UPD, Kt, UPD, Kt))
f10 = w.s([f7, f9], 'mpbid', '( %s -> %s Fn %s )' % (A, UPD, Kt))
A2 = '( %s /\\ k e. %s )' % (A, Kt)
u1 = w.s([], 'uncom', '%s = %s' % (UPD, UPDP)); u2 = w.s([u1], 'fveq1i', '( %s ` k ) = ( %s ` k )' % (UPD, UPDP))
A3 = '( %s /\\ k = K )' % A2
g0 = w.s([], 'eqid', '%s = %s' % (UPDP, UPDP))
gk = w.s([k1], 'ad2antrr', '( %s -> K e. _V )' % A3); gx = w.s([x1], 'ad2antrr', '( %s -> X e. _V )' % A3)
g1 = w.s([gk, gx, g0], 'fvsnun1', '( %s -> ( %s ` K ) = X )' % (A3, UPDP))
g2 = w.s([], 'simpr', '( %s -> k = K )' % A3); g2b = w.s([g2], 'fveq2d', '( %s -> ( %s ` k ) = ( %s ` K ) )' % (A3, UPDP, UPDP))
g3 = w.s([g2b, g1], 'eqtrd', '( %s -> ( %s ` k ) = X )' % (A3, UPDP))
g4 = w.s([a4], 'ad2antrr', '( %s -> X e. %s )' % (A3, WD('K')))
g5 = w.s([g2], 'fveq2d', '( %s -> ( %s ` k ) = ( %s ` K ) )' % (A3, Gt, Gt)); g5i = w.inst('wrdeq')
g5b = w.s([g5, g5i], 'syl', '( %s -> %s = %s )' % (A3, WD('k'), WD('K')))
g6 = w.s([g3, g4], 'eqeltrd', '( %s -> ( %s ` k ) e. %s )' % (A3, UPDP, WD('K')))
g7 = w.s([g6, g5b], 'eleqtrrd', '( %s -> ( %s ` k ) e. %s )' % (A3, UPDP, WD('k')))
A4 = '( %s /\\ k =/= K )' % A2
h0 = w.s([], 'simplr', '( %s -> k e. %s )' % (A4, Kt)); h0b = w.s([], 'simpr', '( %s -> k =/= K )' % A4)
h1e = w.s([], 'eldifsn', '( k e. ( %s \\ { K } ) <-> ( k e. %s /\\ k =/= K ) )' % (Kt, Kt))
h1 = w.s([h0, h0b, h1e], 'sylanbrc', '( %s -> k e. ( %s \\ { K } ) )' % (A4, Kt))
hk = w.s([k1], 'ad2antrr', '( %s -> K e. _V )' % A4); hx = w.s([x1], 'ad2antrr', '( %s -> X e. _V )' % A4)
h2 = w.s([hk, hx, g0, h1], 'fvsnun2', '( %s -> ( %s ` k ) = ( D ` k ) )' % (A4, UPDP))
ht = w.s([a1], 'ad2antrr', '( %s -> T e. V )' % A4); hd = w.s([a2], 'ad2antrr', '( %s -> D e. %s )' % (A4, STK))
h3i = w.inst('tm2stkfv'); h3 = w.s([ht, hd, h0, h3i], 'syl3anc', '( %s -> ( D ` k ) e. %s )' % (A4, WD('k')))
h4 = w.s([h2, h3], 'eqeltrd', '( %s -> ( %s ` k ) e. %s )' % (A4, UPDP, WD('k')))
p = w.s([g7, h4], 'pm2.61dane', '( %s -> ( %s ` k ) e. %s )' % (A2, UPDP, WD('k')))
p2 = w.s([u2, p], 'eqeltrid', '( %s -> ( %s ` k ) e. %s )' % (A2, UPD, WD('k')))
p3 = w.s([p2], 'ralrimiva', '( %s -> A. k e. %s ( %s ` k ) e. %s )' % (A, Kt, UPD, WD('k')))
x0 = w.s([a2], 'elexd', '( %s -> D e. _V )' % A)
x1i = w.inst('resexg'); x2 = w.s([x0, x1i], 'syl', '( %s -> ( D |` ( %s \\ { K } ) ) e. _V )' % (A, Kt))
x3 = w.s([], 'snex', '{ <. K , X >. } e. _V'); x3b = w.s([x3], 'a1i', '( %s -> { <. K , X >. } e. _V )' % A)
x4i = w.inst('unexg'); x4 = w.s([x2, x3b, x4i], 'syl2anc', '( %s -> %s e. _V )' % (A, UPD))
e = w.s([], 'elixp2', '( %s e. %s <-> ( %s e. _V /\\ %s Fn %s /\\ A. k e. %s ( %s ` k ) e. %s ) )' % (UPD, IXP, UPD, UPD, Kt, Kt, UPD, WD('k')))
q = w.s([x4, f10, p3, e], 'syl3anbrc', '( %s -> %s e. %s )' % (A, UPD, IXP))
w.qed([q, v2], 'eleqtrrd', '( %s -> %s e. %s )' % (A, UPD, STK))
run(w)

# ---- tm2stkhead
HEAD = 'if ( ( D ` K ) = (/) , ( inr ` (/) ) , ( inl ` ( ( D ` K ) ` 0 ) ) )'
w = W('tm2stkhead', 'The optional top of a stack (Lean\'s List.head?) is an optional letter of its alphabet.')
A = '( T e. V /\\ D e. %s /\\ K e. %s )' % (STK, Kt)
DJ = '( ( %s ` K ) |_| 1o )' % Gt
c1 = w.s([], '0lt1o', '(/) e. 1o'); c2i = w.inst('djurcl'); c2 = w.s([c1, c2i], 'ax-mp', '( inr ` (/) ) e. %s' % DJ)
c3 = w.s([c2], 'a1i', '( ( %s /\\ ( D ` K ) = (/) ) -> ( inr ` (/) ) e. %s )' % (A, DJ))
A4 = '( %s /\\ -. ( D ` K ) = (/) )' % A
w1i = w.inst('tm2stkfv'); w1a = w.s([w1i], 'adantr', '( %s -> ( D ` K ) e. %s )' % (A4, WD('K')))
w.lines[-1] = w.lines[-1].replace('%s:%s:adantr' % (w1a, w1i), '%s:%s:adantr' % (w1a, w1i))
# fix: instance step can't be used with adantr directly; make explicit
w.lines.pop(); w.lines.pop()
w1 = w.s([], 'tm2stkfv', '( %s -> ( D ` K ) e. %s )' % (A, WD('K')))
w1a = w.s([w1], 'adantr', '( %s -> ( D ` K ) e. %s )' % (A4, WD('K')))
w2s = w.s([], 'simpr', '( %s -> -. ( D ` K ) = (/) )' % A4); w2 = w.s([w2s], 'neqned', '( %s -> ( D ` K ) =/= (/) )' % A4)
w3i = w.inst('lennncl'); w3 = w.s([w1a, w2, w3i], 'syl2anc', '( %s -> ( # ` ( D ` K ) ) e. NN )' % A4)
w4e = w.s([], 'lbfzo0', '( 0 e. ( 0 ..^ ( # ` ( D ` K ) ) ) <-> ( # ` ( D ` K ) ) e. NN )')
w4 = w.s([w3, w4e], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` ( D ` K ) ) ) )' % A4)
w5i = w.inst('wrdf'); w5 = w.s([w1a, w5i], 'syl', '( %s -> ( D ` K ) : ( 0 ..^ ( # ` ( D ` K ) ) ) --> ( %s ` K ) )' % (A4, Gt))
w6i = w.inst('ffvelcdm'); w6 = w.s([w5, w4, w6i], 'syl2anc', '( %s -> ( ( D ` K ) ` 0 ) e. ( %s ` K ) )' % (A4, Gt))
w7i = w.inst('djulcl'); w7 = w.s([w6, w7i], 'syl', '( %s -> ( inl ` ( ( D ` K ) ` 0 ) ) e. %s )' % (A4, DJ))
w.qed([c3, w7], 'ifclda', '( %s -> %s e. %s )' % (A, HEAD, DJ))
run(w)

# ---- tm2safnval
w = W('tm2safnval', 'The depth-N function agrees with TM2sa on depth-N statements.')
A = '( ( T e. V /\\ N e. _om ) /\\ ( R e. %s /\\ Y e. %s ) )' % (LYn('N'), PRT)
a1 = w.s([], 'simpll', '( %s -> T e. V )' % A); a2 = w.s([], 'simplr', '( %s -> N e. _om )' % A)
a3 = w.s([], 'simprl', '( %s -> R e. %s )' % (A, LYn('N'))); a4 = w.s([], 'simprr', '( %s -> Y e. %s )' % (A, PRT))
b1i = w.inst('tm2safun'); b1 = w.s([a1, b1i], 'syl', '( %s -> Fun %s )' % (A, SAT))
b2i = w.inst('tm2sassa'); b2 = w.s([a1, a2, b2i], 'syl2anc', '( %s -> %s C_ %s )' % (A, FN_('N'), SAT))
b3i = w.inst('tm2safn'); b3 = w.s([a1, a2, b3i], 'syl2anc', '( %s -> %s Fn ( %s X. %s ) )' % (A, FN_('N'), LYn('N'), PRT))
b4i = w.inst('fndm'); b4 = w.s([b3, b4i], 'syl', '( %s -> dom %s = ( %s X. %s ) )' % (A, FN_('N'), LYn('N'), PRT))
b5i = w.inst('opelxpi'); b5 = w.s([a3, a4, b5i], 'syl2anc', '( %s -> <. R , Y >. e. ( %s X. %s ) )' % (A, LYn('N'), PRT))
b6 = w.s([b5, b4], 'eleqtrrd', '( %s -> <. R , Y >. e. dom %s )' % (A, FN_('N')))
b7i = w.inst('funssfv'); b7 = w.s([b1, b2, b6, b7i], 'syl3anc', '( %s -> ( %s ` <. R , Y >. ) = ( %s ` <. R , Y >. ) )' % (A, SAT, FN_('N')))
b8 = w.s([b7], 'eqcomd', '( %s -> ( %s ` <. R , Y >. ) = ( %s ` <. R , Y >. ) )' % (A, FN_('N'), SAT))
c1 = w.s([], 'df-ov', '( R %s Y ) = ( %s ` <. R , Y >. )' % (FN_('N'), FN_('N')))
c2 = w.s([], 'df-ov', '( R %s Y ) = ( %s ` <. R , Y >. )' % (SAT, SAT))
c3 = w.s([c1, b8], 'eqtrid', '( %s -> ( R %s Y ) = ( %s ` <. R , Y >. ) )' % (A, FN_('N'), SAT))
w.qed([c3, c2], 'eqtr4di', '( %s -> ( R %s Y ) = ( R %s Y ) )' % (A, FN_('N'), SAT))
run(w)
