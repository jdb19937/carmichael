"""Sortie C0, batch 8: the closed axis-parallel rectangle and its boundary
integral (crectval, elcrect, crectss, crectcvx, crectcnr1-4, rectintval,
rectintcl, rectintftc)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w, h=False):
    if only and w.label not in only: return True
    return runh(w) if h else w.run()

def RI(X, Y): return '( ( Re ` %s ) [,] ( Re ` %s ) )' % (X, Y)
def II(X, Y): return '( ( Im ` %s ) [,] ( Im ` %s ) )' % (X, Y)
def RB(X, Y): return '{ z e. CC | ( ( Re ` z ) e. %s /\\ ( Im ` z ) e. %s ) }' % (RI(X, Y), II(X, Y))
AB = '( A e. CC /\\ B e. CC )'
PR = '( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) )'

# ---- crectval
w = W('crectval', 'Value of the closed rectangle with given corners.')
E = '( a = A /\\ b = B )'
la = w.s([], 'simpl', '( %s -> a = A )' % E); lb = w.s([], 'simpr', '( %s -> b = B )' % E)
for part in ('Re', 'Im'):
    w.s([la], 'fveq2d', '( %s -> ( %s ` a ) = ( %s ` A ) )' % (E, part, part), name='%sa' % part)
    w.s([lb], 'fveq2d', '( %s -> ( %s ` b ) = ( %s ` B ) )' % (E, part, part), name='%sb' % part)
oi1 = w.s(['Rea', 'Reb'], 'oveq12d', '( %s -> %s = %s )' % (E, RI('a', 'b'), RI('A', 'B')))
oi2 = w.s(['Ima', 'Imb'], 'oveq12d', '( %s -> %s = %s )' % (E, II('a', 'b'), II('A', 'B')))
b1 = w.s([oi1], 'eleq2d', '( %s -> ( ( Re ` z ) e. %s <-> ( Re ` z ) e. %s ) )' % (E, RI('a', 'b'), RI('A', 'B')))
b2 = w.s([oi2], 'eleq2d', '( %s -> ( ( Im ` z ) e. %s <-> ( Im ` z ) e. %s ) )' % (E, II('a', 'b'), II('A', 'B')))
an = w.s([b1, b2], 'anbi12d', '( %s -> ( ( ( Re ` z ) e. %s /\\ ( Im ` z ) e. %s ) <-> ( ( Re ` z ) e. %s /\\ ( Im ` z ) e. %s ) ) )' % (E, RI('a', 'b'), II('a', 'b'), RI('A', 'B'), II('A', 'B')))
rb = w.s([an], 'rabbidv', '( %s -> %s = %s )' % (E, RB('a', 'b'), RB('A', 'B')))
d = w.s([], 'df-crect', 'crect = ( a e. CC , b e. CC |-> %s )' % RB('a', 'b'))
cx = w.s([], 'cnex', 'CC e. _V')
rx = w.s([cx, w.inst('rabexg')], 'ax-mp', '%s e. _V' % RB('A', 'B'))
o = w.s([rb, d], 'ovmpoga', '( ( A e. CC /\\ B e. CC /\\ %s e. _V ) -> ( A crect B ) = %s )' % (RB('A', 'B'), RB('A', 'B')))
w.qed([rx, o], 'mp3an3', '( %s -> ( A crect B ) = %s )' % (AB, RB('A', 'B'))); run(w)

# ---- elcrect
w = W('elcrect', 'Membership in a closed rectangle.')
v = w.s([], 'crectval', '( %s -> ( A crect B ) = %s )' % (AB, RB('A', 'B')))
e = w.s([v], 'eleq2d', '( %s -> ( Z e. ( A crect B ) <-> Z e. %s ) )' % (AB, RB('A', 'B')))
for part in ('Re', 'Im'):
    w.s([], 'fveq2', '( z = Z -> ( %s ` z ) = ( %s ` Z ) )' % (part, part), name='f%s' % part)
s1 = w.s(['fRe'], 'eleq1d', '( z = Z -> ( ( Re ` z ) e. %s <-> ( Re ` Z ) e. %s ) )' % (RI('A', 'B'), RI('A', 'B')))
s2 = w.s(['fIm'], 'eleq1d', '( z = Z -> ( ( Im ` z ) e. %s <-> ( Im ` Z ) e. %s ) )' % (II('A', 'B'), II('A', 'B')))
sa = w.s([s1, s2], 'anbi12d', '( z = Z -> ( ( ( Re ` z ) e. %s /\\ ( Im ` z ) e. %s ) <-> ( ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) ) )' % (RI('A', 'B'), II('A', 'B'), RI('A', 'B'), II('A', 'B')))
er = w.s([sa], 'elrab', '( Z e. %s <-> ( Z e. CC /\\ ( ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) ) )' % (RB('A', 'B'), RI('A', 'B'), II('A', 'B')))
erd = w.s([er], 'a1i', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ ( ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) ) ) )' % (AB, RB('A', 'B'), RI('A', 'B'), II('A', 'B')))
bt = w.s([e, erd], 'bitrd', '( %s -> ( Z e. ( A crect B ) <-> ( Z e. CC /\\ ( ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) ) ) )' % (AB, RI('A', 'B'), II('A', 'B')))
a3 = closed(w, AB, '3anass', '( ( Z e. CC /\\ ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) <-> ( Z e. CC /\\ ( ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) ) )' % (RI('A', 'B'), II('A', 'B'), RI('A', 'B'), II('A', 'B')))
w.qed([bt, a3], 'bitr4d', '( %s -> ( Z e. ( A crect B ) <-> ( Z e. CC /\\ ( Re ` Z ) e. %s /\\ ( Im ` Z ) e. %s ) ) )' % (AB, RI('A', 'B'), II('A', 'B'))); run(w)

# ---- crectss
w = W('crectss', 'A closed rectangle is a set of complex numbers.')
v = w.s([], 'crectval', '( %s -> ( A crect B ) = %s )' % (AB, RB('A', 'B')))
sr = closed(w, AB, 'ssrab2', '%s C_ CC' % RB('A', 'B'))
w.qed([v, sr], 'eqsstrd', '( %s -> ( A crect B ) C_ CC )' % AB); run(w)

# ---- crectcvx
w = W('crectcvx', 'A closed rectangle is convex: the segment between two of its points lies in it.')
A = '( %s /\\ ( X e. ( A crect B ) /\\ Y e. ( A crect B ) ) )' % AB
A2 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A
ab = w.s([], 'simpl', '( %s -> %s )' % (A, AB))
xr = w.s([], 'simprl', '( %s -> X e. ( A crect B ) )' % A); yr = w.s([], 'simprr', '( %s -> Y e. ( A crect B ) )' % A)
elc = w.s([ab, w.inst('elcrect')], 'syl', '( %s -> ( X e. ( A crect B ) <-> ( X e. CC /\\ ( Re ` X ) e. %s /\\ ( Im ` X ) e. %s ) ) )' % (A, RI('A', 'B'), II('A', 'B')))
tx = w.s([xr, elc], 'mpbid', '( %s -> ( X e. CC /\\ ( Re ` X ) e. %s /\\ ( Im ` X ) e. %s ) )' % (A, RI('A', 'B'), II('A', 'B')))
elc2 = w.s([ab, w.inst('elcrect')], 'syl', '( %s -> ( Y e. ( A crect B ) <-> ( Y e. CC /\\ ( Re ` Y ) e. %s /\\ ( Im ` Y ) e. %s ) ) )' % (A, RI('A', 'B'), II('A', 'B')))
ty = w.s([yr, elc2], 'mpbid', '( %s -> ( Y e. CC /\\ ( Re ` Y ) e. %s /\\ ( Im ` Y ) e. %s ) )' % (A, RI('A', 'B'), II('A', 'B')))
xc = w.s([tx, w.inst('simp1')], 'syl', '( %s -> X e. CC )' % A); yc = w.s([ty, w.inst('simp1')], 'syl', '( %s -> Y e. CC )' % A)
xre = w.s([tx, w.inst('simp2')], 'syl', '( %s -> ( Re ` X ) e. %s )' % (A, RI('A', 'B')))
xim = w.s([tx, w.inst('simp3')], 'syl', '( %s -> ( Im ` X ) e. %s )' % (A, II('A', 'B')))
yre = w.s([ty, w.inst('simp2')], 'syl', '( %s -> ( Re ` Y ) e. %s )' % (A, RI('A', 'B')))
yim = w.s([ty, w.inst('simp3')], 'syl', '( %s -> ( Im ` Y ) e. %s )' % (A, II('A', 'B')))
L = LIN('X', 'Y')
xc2 = w.s([xc], 'adantr', '( %s -> X e. CC )' % A2); yc2 = w.s([yc], 'adantr', '( %s -> Y e. CC )' % A2)
tt = w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A2)
tr = w.s([tt, w.inst('elunitrn')], 'syl', '( %s -> t e. RR )' % A2)
tc = w.s([tt, w.inst('elunitcn')], 'syl', '( %s -> t e. CC )' % A2)
lcc = w.s([xc2, w.s([tc, w.s([yc2, xc2], 'subcld', '( %s -> ( Y - X ) e. CC )' % A2)], 'mulcld', '( %s -> ( t x. ( Y - X ) ) e. CC )' % A2)], 'addcld', '( %s -> %s e. CC )' % (A2, L))
for part, lin, cv in (('Re', 'cseglinre', 'RI'), ('Im', 'cseglinim', 'II')):
    intv = RI('A', 'B') if part == 'Re' else II('A', 'B')
    pl = w.s([xc2, yc2, tr, w.inst(lin)], 'syl3anc', '( %s -> ( %s ` %s ) = ( ( %s ` X ) + ( t x. ( ( %s ` Y ) - ( %s ` X ) ) ) ) )' % (A2, part, L, part, part, part))
    pxc = w.s([w.s([xc2, w.inst({'Re': 'recl', 'Im': 'imcl'}[part])], 'syl', '( %s -> ( %s ` X ) e. RR )' % (A2, part))], 'recnd', '( %s -> ( %s ` X ) e. CC )' % (A2, part))
    pyc = w.s([w.s([yc2, w.inst({'Re': 'recl', 'Im': 'imcl'}[part])], 'syl', '( %s -> ( %s ` Y ) e. RR )' % (A2, part))], 'recnd', '( %s -> ( %s ` Y ) e. CC )' % (A2, part))
    cvx = w.s([pxc, pyc, tc, w.inst('cvxid')], 'syl3anc', '( %s -> ( ( %s ` X ) + ( t x. ( ( %s ` Y ) - ( %s ` X ) ) ) ) = ( ( ( 1 - t ) x. ( %s ` X ) ) + ( t x. ( %s ` Y ) ) ) )' % (A2, part, part, part, part, part))
    ar = w.s([w.s([ab, w.inst({'Re': 'simpl', 'Im': 'simpl'}[part])], 'syl', '( %s -> A e. CC )' % A)], 'adantr', '( %s -> A e. CC )' % A2)
    br = w.s([w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A)], 'adantr', '( %s -> B e. CC )' % A2)
    arr = w.s([ar, w.inst({'Re': 'recl', 'Im': 'imcl'}[part])], 'syl', '( %s -> ( %s ` A ) e. RR )' % (A2, part))
    brr = w.s([br, w.inst({'Re': 'recl', 'Im': 'imcl'}[part])], 'syl', '( %s -> ( %s ` B ) e. RR )' % (A2, part))
    jj = w.s([arr, brr], 'jca', '( %s -> ( ( %s ` A ) e. RR /\\ ( %s ` B ) e. RR ) )' % (A2, part, part))
    ci = w.s([jj, w.inst('icccvx')], 'syl', '( %s -> ( ( ( %s ` X ) e. %s /\\ ( %s ` Y ) e. %s /\\ t e. ( 0 [,] 1 ) ) -> ( ( ( 1 - t ) x. ( %s ` X ) ) + ( t x. ( %s ` Y ) ) ) e. %s ) )' % (A2, part, intv, part, intv, part, part, intv))
    px = w.s([xre if part == 'Re' else xim], 'adantr', '( %s -> ( %s ` X ) e. %s )' % (A2, part, intv))
    py = w.s([yre if part == 'Re' else yim], 'adantr', '( %s -> ( %s ` Y ) e. %s )' % (A2, part, intv))
    cc2 = w.s([px, py, tt, ci], 'mp3and', '( %s -> ( ( ( 1 - t ) x. ( %s ` X ) ) + ( t x. ( %s ` Y ) ) ) e. %s )' % (A2, part, part, intv))
    ch = w.s([w.s([pl, cvx], 'eqtrd', '( %s -> ( %s ` %s ) = ( ( ( 1 - t ) x. ( %s ` X ) ) + ( t x. ( %s ` Y ) ) ) )' % (A2, part, L, part, part)), cc2], 'eqeltrd', '( %s -> ( %s ` %s ) e. %s )' % (A2, part, L, intv), name='in%s' % part)
ab2 = w.s([ab], 'adantr', '( %s -> %s )' % (A2, AB))
elc3 = w.s([ab2, w.inst('elcrect')], 'syl', '( %s -> ( %s e. ( A crect B ) <-> ( %s e. CC /\\ ( Re ` %s ) e. %s /\\ ( Im ` %s ) e. %s ) ) )' % (A2, L, L, L, RI('A', 'B'), L, II('A', 'B')))
mem = w.s([lcc, 'inRe', 'inIm', elc3], 'mpbir3and', '( %s -> %s e. ( A crect B ) )' % (A2, L))
e1 = w.s([], 'eleq1', '( x = %s -> ( x e. ( A crect B ) <-> %s e. ( A crect B ) ) )' % (L, L))
i1 = w.s([mem, e1], 'syl5ibrcom', '( %s -> ( x = %s -> x e. ( A crect B ) ) )' % (A2, L))
r = w.s([i1], 'rexlimdva', '( %s -> ( E. t e. ( 0 [,] 1 ) x = %s -> x e. ( A crect B ) ) )' % (A, L))
m = w.s([xc, yc, w.inst('csegel')], 'syl2anc', '( %s -> ( x e. ( X cseg Y ) <-> E. t e. ( 0 [,] 1 ) x = %s ) )' % (A, L))
s = w.s([m, r], 'sylbid', '( %s -> ( x e. ( X cseg Y ) -> x e. ( A crect B ) ) )' % A)
w.qed([s], 'ssrdv', '( %s -> ( X cseg Y ) C_ ( A crect B ) )' % A); run(w)

# ---- crectcnr1 .. crectcnr4: the four corners lie in the rectangle
def cornerws(lbl, Z, rev, imv, desc):
    w = W(lbl, desc)
    ab = w.s([], 'simpl', '( %s -> %s )' % (PR, AB))
    a = w.s([], 'simpll', '( %s -> A e. CC )' % PR); b = w.s([], 'simplr', '( %s -> B e. CC )' % PR)
    rle = w.s([], 'simprl', '( %s -> ( Re ` A ) <_ ( Re ` B ) )' % PR)
    ile = w.s([], 'simprr', '( %s -> ( Im ` A ) <_ ( Im ` B ) )' % PR)
    reA = w.s([a, w.inst('recl')], 'syl', '( %s -> ( Re ` A ) e. RR )' % PR)
    reB = w.s([b, w.inst('recl')], 'syl', '( %s -> ( Re ` B ) e. RR )' % PR)
    imA = w.s([a, w.inst('imcl')], 'syl', '( %s -> ( Im ` A ) e. RR )' % PR)
    imB = w.s([b, w.inst('imcl')], 'syl', '( %s -> ( Im ` B ) e. RR )' % PR)
    xrA = w.s([reA], 'rexrd', '( %s -> ( Re ` A ) e. RR* )' % PR)
    xrB = w.s([reB], 'rexrd', '( %s -> ( Re ` B ) e. RR* )' % PR)
    yrA = w.s([imA], 'rexrd', '( %s -> ( Im ` A ) e. RR* )' % PR)
    yrB = w.s([imB], 'rexrd', '( %s -> ( Im ` B ) e. RR* )' % PR)
    mre = w.s([xrA, xrB, rle, w.inst('lbicc2' if rev == '( Re ` A )' else 'ubicc2')], 'syl3anc', '( %s -> %s e. %s )' % (PR, rev, RI('A', 'B')))
    mim = w.s([yrA, yrB, ile, w.inst('lbicc2' if imv == '( Im ` A )' else 'ubicc2')], 'syl3anc', '( %s -> %s e. %s )' % (PR, imv, II('A', 'B')))
    if Z in ('A', 'B'):
        zc = a if Z == 'A' else b
        zre = w.s([], 'eqidd', '( %s -> ( Re ` %s ) = %s )' % (PR, Z, rev))
        zim = w.s([], 'eqidd', '( %s -> ( Im ` %s ) = %s )' % (PR, Z, imv))
    else:
        rst = reB if rev == '( Re ` B )' else reA
        ist = imA if imv == '( Im ` A )' else imB
        ic = closed(w, PR, 'ax-icn', '_i e. CC')
        p1 = w.s([rst], 'recnd', '( %s -> %s e. CC )' % (PR, rev))
        p2 = w.s([ist], 'recnd', '( %s -> %s e. CC )' % (PR, imv))
        m = w.s([ic, p2], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (PR, imv))
        zc = w.s([p1, m], 'addcld', '( %s -> %s e. CC )' % (PR, Z))
        zre = w.s([rst, ist, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (PR, Z, rev))
        zim = w.s([rst, ist, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (PR, Z, imv))
    rez = w.s([zre, mre], 'eqeltrd', '( %s -> ( Re ` %s ) e. %s )' % (PR, Z, RI('A', 'B')))
    imz = w.s([zim, mim], 'eqeltrd', '( %s -> ( Im ` %s ) e. %s )' % (PR, Z, II('A', 'B')))
    elc = w.s([ab, w.inst('elcrect')], 'syl', '( %s -> ( %s e. ( A crect B ) <-> ( %s e. CC /\\ ( Re ` %s ) e. %s /\\ ( Im ` %s ) e. %s ) ) )' % (PR, Z, Z, Z, RI('A', 'B'), Z, II('A', 'B')))
    w.qed([zc, rez, imz, elc], 'mpbir3and', '( %s -> %s e. ( A crect B ) )' % (PR, Z))
    return run(w)


cornerws('crectcnr1', 'A', '( Re ` A )', '( Im ` A )', 'The lower left corner lies in the rectangle.')
cornerws('crectcnr2', B1('A', 'B'), '( Re ` B )', '( Im ` A )', 'The lower right corner lies in the rectangle.')
cornerws('crectcnr3', 'B', '( Re ` B )', '( Im ` B )', 'The upper right corner lies in the rectangle.')
cornerws('crectcnr4', A1('A', 'B'), '( Re ` A )', '( Im ` B )', 'The upper left corner lies in the rectangle.')

# ---- rectintval
w = W('rectintval', 'Value of the boundary integral around a rectangle: the four segment integrals along its edges, counter-clockwise from the lower left corner.')
A = '( F e. V /\\ A e. CC /\\ B e. CC )'; E = '( f = F /\\ p = <. A , B >. )'
f = w.s([], 'simp1', '( %s -> F e. V )' % A); a = w.s([], 'simp2', '( %s -> A e. CC )' % A); b = w.s([], 'simp3', '( %s -> B e. CC )' % A)
P1 = '( 1st ` p )'; P2 = '( 2nd ` p )'
BRp = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (P2, P1)
ALp = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (P1, P2)
R = ('( ( ( f lint <. %s , %s >. ) + ( f lint <. %s , %s >. ) ) + ( ( f lint <. %s , %s >. ) + ( f lint <. %s , %s >. ) ) )'
     % (P1, BRp, BRp, P2, P2, ALp, ALp, P1))
d = w.s([], 'df-rectint', 'rectint = ( f e. _V , p e. ( CC X. CC ) |-> %s )' % R)
dd = w.s([d], 'a1i', '( %s -> rectint = ( f e. _V , p e. ( CC X. CC ) |-> %s ) )' % (A, R))
lf = w.s([], 'simpl', '( %s -> f = F )' % E); lp = w.s([], 'simpr', '( %s -> p = <. A , B >. )' % E)
c, R1 = w.congr(R, {'f': 'F', 'p': '<. A , B >.'}, E, {'f': lf, 'p': lp})
c2 = w.s([c], 'adantl', '( ( %s /\\ %s ) -> %s = %s )' % (A, E, R, R1))
ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A); bx = w.s([b], 'elexd', '( %s -> B e. _V )' % A)
ev, R2 = evaluate(w, A, R1, {'A': ax, 'B': bx})
EXP = ('( ( ( F lint <. A , %s >. ) + ( F lint <. %s , B >. ) ) + ( ( F lint <. B , %s >. ) + ( F lint <. %s , A >. ) ) )'
       % (B1('A', 'B'), B1('A', 'B'), A1('A', 'B'), A1('A', 'B')))
assert R2 == EXP, R2
ev2 = w.s([ev], 'adantr', '( ( %s /\\ %s ) -> %s = %s )' % (A, E, R1, R2))
c5 = w.s([c2, ev2], 'eqtrd', '( ( %s /\\ %s ) -> %s = %s )' % (A, E, R, R2))
fx = w.s([f], 'elexd', '( %s -> F e. _V )' % A)
op = w.s([a, b, w.inst('opelxpi')], 'syl2anc', '( %s -> <. A , B >. e. ( CC X. CC ) )' % A)
ix = closed(w, A, 'ovex', '%s e. _V' % R2)
w.qed([dd, c5, fx, op, ix], 'ovmpod', '( %s -> %s = %s )' % (A, RINT('F', 'A', 'B'), R2)); run(w)

CORNERS = ['A', B1('A', 'B'), 'B', A1('A', 'B')]
CNRLAB = ['crectcnr1', 'crectcnr2', 'crectcnr3', 'crectcnr4']
SEGS = [(0, 1), (1, 2), (2, 3), (3, 0)]


def rectctx(w, ante, dom, domss):
    """steps for the four corners (in CC, in the rectangle) and the four edges
    (segment inclusion in dom)"""
    ab = w.s([], 'simp1', '( %s -> %s )' % (ante, AB))
    bd = w.s([], 'simp2', '( %s -> ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) )' % ante)
    pr = w.s([ab, bd], 'jca', '( %s -> %s )' % (ante, PR))
    ss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % ante)
    inr = []; cc = []
    for Z, lbl in zip(CORNERS, CNRLAB):
        st = w.s([pr, w.inst(lbl)], 'syl', '( %s -> %s e. ( A crect B ) )' % (ante, Z))
        inr.append(st)
        cc.append(w.s([ss, st], 'sseldd', '( %s -> %s e. CC )' % (ante, Z)))
    segss = []
    for i, j in SEGS:
        X, Y = CORNERS[i], CORNERS[j]
        jj = w.s([inr[i], inr[j]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (ante, X, Y))
        aj = w.s([ab, jj], 'jca', '( %s -> ( %s /\\ ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) ) )' % (ante, AB, X, Y))
        cv = w.s([aj, w.inst('crectcvx')], 'syl', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (ante, X, Y))
        segss.append(w.s([cv, domss], 'sstrd', '( %s -> ( %s cseg %s ) C_ %s )' % (ante, X, Y, dom)))
    return ab, cc, inr, segss


# ---- rectintcl
PSR = ('( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) /\\ '
       '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )')
w = W('rectintcl', 'Closure of the boundary integral around a rectangle contained in the domain of continuity.')
fcn = w.s([], 'simp3l', '( %s -> F e. ( D -cn-> CC ) )' % PSR)
dss = w.s([], 'simp3r', '( %s -> ( A crect B ) C_ D )' % PSR)
ab, cc, inr, segss = rectctx(w, PSR, 'D', dss)
a = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % PSR)
b = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % PSR)
terms = []
for k, (i, j) in enumerate(SEGS):
    X, Y = CORNERS[i], CORNERS[j]
    j1 = w.s([cc[i], cc[j]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (PSR, X, Y))
    j2 = w.s([fcn, segss[k]], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (PSR, X, Y))
    j3 = w.s([j1, j2], 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) ) )' % (PSR, X, Y, X, Y))
    terms.append(w.s([j3, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (PSR, LINT('F', X, Y))))
s1 = w.s([terms[0], terms[1]], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (PSR, LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2])))
s2 = w.s([terms[2], terms[3]], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (PSR, LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0])))
sm = w.s([s1, s2], 'addcld', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) e. CC )' % (PSR, LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0])))
v = w.s([fcn, a, b, w.inst('rectintval')], 'syl3anc', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (PSR, RINT('F', 'A', 'B'), LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0])))
w.qed([v, sm], 'eqeltrd', '( %s -> %s e. CC )' % (PSR, RINT('F', 'A', 'B'))); run(w)

# ---- rectintftc
PSF = ('( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) /\\ '
       '( ( G : U --> CC /\\ ( CC _D G ) = F ) /\\ ( F e. ( U -cn-> CC ) /\\ ( A crect B ) C_ U ) ) )')
w = W('rectintftc', 'The boundary integral around a rectangle of a function with a primitive on an open set containing the rectangle is zero.')
gdv = w.s([], 'simp3l', '( %s -> ( G : U --> CC /\\ ( CC _D G ) = F ) )' % PSF)
fcn = w.s([], 'simp3rl', '( %s -> F e. ( U -cn-> CC ) )' % PSF)
uss = w.s([], 'simp3rr', '( %s -> ( A crect B ) C_ U )' % PSF)
gf = w.s([gdv, w.inst('simpl')], 'syl', '( %s -> G : U --> CC )' % PSF)
ab, cc, inr, segss = rectctx(w, PSF, 'U', uss)
a = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % PSF)
b = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % PSF)
gv = []
for k, Z in enumerate(CORNERS):
    zu = w.s([uss, inr[k]], 'sseldd', '( %s -> %s e. U )' % (PSF, Z))
    gv.append(w.s([gf, zu], 'ffvelcdmd', '( %s -> ( G ` %s ) e. CC )' % (PSF, Z)))
eqs = []
for k, (i, j) in enumerate(SEGS):
    X, Y = CORNERS[i], CORNERS[j]
    j1 = w.s([cc[i], cc[j]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (PSF, X, Y))
    j2 = w.s([fcn, segss[k]], 'jca', '( %s -> ( F e. ( U -cn-> CC ) /\\ ( %s cseg %s ) C_ U ) )' % (PSF, X, Y))
    eqs.append(w.s([j1, gdv, j2, w.inst('lintftc')], 'syl3anc', '( %s -> %s = ( ( G ` %s ) - ( G ` %s ) ) )' % (PSF, LINT('F', X, Y), Y, X)))
def DF(i, j): return '( ( G ` %s ) - ( G ` %s ) )' % (CORNERS[j], CORNERS[i])
o1 = w.s([eqs[0], eqs[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (PSF, LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), DF(0, 1), DF(1, 2)))
o2 = w.s([eqs[2], eqs[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (PSF, LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0]), DF(2, 3), DF(3, 0)))
BA = '( ( G ` B ) - ( G ` A ) )'; AB2 = '( ( G ` A ) - ( G ` B ) )'
n1 = w.s([gv[1], gv[0], gv[2]], 'npncan3d', '( %s -> ( %s + %s ) = %s )' % (PSF, DF(0, 1), DF(1, 2), BA))
n2 = w.s([gv[3], gv[2], gv[0]], 'npncan3d', '( %s -> ( %s + %s ) = %s )' % (PSF, DF(2, 3), DF(3, 0), AB2))
z = w.s([gv[2], gv[0], w.inst('npncan2')], 'syl2anc', '( %s -> ( %s + %s ) = 0 )' % (PSF, BA, AB2))
h1 = w.s([o1, n1], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (PSF, LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), BA))
h2 = w.s([o2, n2], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (PSF, LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0]), AB2))
o3 = w.s([h1, h2], 'oveq12d', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = ( %s + %s ) )' % (PSF, LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0]), BA, AB2))
tot = w.s([o3, z], 'eqtrd', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = 0 )' % (PSF, LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0])))
v = w.s([fcn, a, b, w.inst('rectintval')], 'syl3anc', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (PSF, RINT('F', 'A', 'B'), LINT('F', CORNERS[0], CORNERS[1]), LINT('F', CORNERS[1], CORNERS[2]), LINT('F', CORNERS[2], CORNERS[3]), LINT('F', CORNERS[3], CORNERS[0])))
w.qed([v, tot], 'eqtrd', '( %s -> %s = 0 )' % (PSF, RINT('F', 'A', 'B'))); run(w)
