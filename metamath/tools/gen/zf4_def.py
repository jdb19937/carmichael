"""Sortie ZF4, batch 1: the Gauss sum unfolded (Mathlib gaussSum with
ZMod.stdAddChar), the additive character as a power of set.mm's root of
unity, closure."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from zf4lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

RN = R('N')
# ---- root1cl
w = W('root1cl', 'The primitive N-th root of unity of set.mm (root1id) is a nonzero complex number.')
m1 = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( N e. NN -> -u 1 e. CC )')
m1n = w.s([w.s([], 'neg1ne0', '-u 1 =/= 0')], 'a1i', '( N e. NN -> -u 1 =/= 0 )')
n = w.s([], 'id', '( N e. NN -> N e. NN )')
q = w.s([w.s([], '2cnd', '( N e. NN -> 2 e. CC )'), w.s([n], 'nncnd', '( N e. NN -> N e. CC )'), w.s([n], 'nnne0d', '( N e. NN -> N =/= 0 )')], 'divcld', '( N e. NN -> ( 2 / N ) e. CC )')
c = w.s([m1, q], 'cxpcld', '( N e. NN -> %s e. CC )' % RN)
ne = w.s([m1, m1n, q], 'cxpne0d', '( N e. NN -> %s =/= 0 )' % RN)
w.qed([c, ne], 'jca', '( N e. NN -> ( %s e. CC /\\ %s =/= 0 ) )' % (RN, RN)); run(w)

# ---- root1expcl
A0 = '( N e. NN /\\ K e. ZZ )'
w = W('root1expcl', 'Integer powers of the root of unity are complex numbers.')
cl = w.s([w.s([], 'simpl', '( %s -> N e. NN )' % A0), w.inst('root1cl')], 'syl', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A0, RN, RN))
w.qed([w.s([cl], 'simpld', '( %s -> %s e. CC )' % (A0, RN)), w.s([cl], 'simprd', '( %s -> %s =/= 0 )' % (A0, RN)), w.s([], 'simpr', '( %s -> K e. ZZ )' % A0)], 'expclzd', '( %s -> %s e. CC )' % (A0, RP('K'))); run(w)

# ---- dchrgsval: the definition unfolded (ovmpodx, dependent second domain)
T = GS('N', 'X'); BODY = GSBODY('N', 'X')
w = W('dchrgsval', 'Value of the Gauss sum of a Dirichlet character X mod N (Mathlib gaussSum chi ZMod.stdAddChar): the sum over the residues a in ( 0 ..^ N ) of X at the class of a times exp ( 2 _pi _i a / N ).')
n = w.s([], 'simpl', '( %s -> N e. NN )' % HC); x = w.s([], 'simpr', '( %s -> X e. %s )' % (HC, DB('N')))
d0 = w.s([], 'df-dchrgs', 'DChrGS = %s' % GSMPO())
d1 = w.s([d0], 'a1i', '( %s -> DChrGS = %s )' % (HC, GSMPO()))
A2 = '( %s /\\ ( n = N /\\ x = X ) )' % HC
ln = w.s([], 'simprl', '( %s -> n = N )' % A2); lx = w.s([], 'simprr', '( %s -> x = X )' % A2)
c, new = w.congr(GSBODY('n', 'x'), {'n': 'N', 'x': 'X'}, A2, {'n': ln, 'x': lx})
assert new == BODY, new
A1 = '( %s /\\ n = N )' % HC
dom = w.s([w.s([w.s([], 'simpr', '( %s -> n = N )' % A1)], 'fveq2d', '( %s -> ( DChr ` n ) = ( DChr ` N ) )' % A1)], 'fveq2d', '( %s -> %s = %s )' % (A1, DB('n'), DB('N')))
ex = w.s([w.s([], 'sumex', '%s e. _V' % BODY)], 'a1i', '( %s -> %s e. _V )' % (HC, BODY))
w.qed([d1, c, dom, n, x, ex], 'ovmpodx', '( %s -> %s = %s )' % (HC, T, BODY)); run(w)

# ---- dchrgsef: the additive character is a power of the root of unity
A0 = '( N e. NN /\\ A e. ZZ )'
I = '( _i x. _pi )'; Q = '( ( 2 / N ) x. %s )' % I
w = W('dchrgsef', 'The additive character exp ( 2 _pi _i A / N ) (Mathlib ZMod.stdAddChar at the class of A) is the A-th power of the primitive N-th root of unity ( -u 1 ^c ( 2 / N ) ).')
n = w.s([], 'simpl', '( %s -> N e. NN )' % A0); a = w.s([], 'simpr', '( %s -> A e. ZZ )' % A0)
ncn = w.s([n], 'nncnd', '( %s -> N e. CC )' % A0); nne = w.s([n], 'nnne0d', '( %s -> N =/= 0 )' % A0)
acn = w.s([a], 'zcnd', '( %s -> A e. CC )' % A0); two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
icn = w.s([w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '%s e. CC' % I)], 'a1i', '( %s -> %s e. CC )' % (A0, I))
q = w.s([two, ncn, nne], 'divcld', '( %s -> ( 2 / N ) e. CC )' % A0)
qcn = w.s([q, icn], 'mulcld', '( %s -> %s e. CC )' % (A0, Q))
m1 = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % A0)
m1n = w.s([w.s([], 'neg1ne0', '-u 1 =/= 0')], 'a1i', '( %s -> -u 1 =/= 0 )' % A0)
r1 = w.s([m1, m1n, q, w.inst('cxpef')], 'syl3anc', '( %s -> %s = ( exp ` ( ( 2 / N ) x. ( log ` -u 1 ) ) ) )' % (A0, RN))
lg = w.s([w.s([w.s([], 'logm1', '( log ` -u 1 ) = %s' % I)], 'a1i', '( %s -> ( log ` -u 1 ) = %s )' % (A0, I))], 'oveq2d', '( %s -> ( ( 2 / N ) x. ( log ` -u 1 ) ) = %s )' % (A0, Q))
r2 = w.s([r1, w.s([lg], 'fveq2d', '( %s -> ( exp ` ( ( 2 / N ) x. ( log ` -u 1 ) ) ) = ( exp ` %s ) )' % (A0, Q))], 'eqtrd', '( %s -> %s = ( exp ` %s ) )' % (A0, RN, Q))
r3 = w.s([r2], 'oveq1d', '( %s -> %s = ( ( exp ` %s ) ^ A ) )' % (A0, RP('A'), Q))
ef = w.s([qcn, a, w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` ( A x. %s ) ) = ( ( exp ` %s ) ^ A ) )' % (A0, Q, Q))
# ( 2 x. I ) x. ( A / N ) = A x. ( ( 2 / N ) x. I )
TI = '( 2 x. %s )' % I
ticn = w.s([two, icn], 'mulcld', '( %s -> %s e. CC )' % (A0, TI))
e1 = w.s([w.s([ticn, acn, ncn, nne], 'divassd', '( %s -> ( ( %s x. A ) / N ) = ( %s x. ( A / N ) ) )' % (A0, TI, TI))], 'eqcomd', '( %s -> ( %s x. ( A / N ) ) = ( ( %s x. A ) / N ) )' % (A0, TI, TI))
e2 = w.s([w.s([two, icn, acn], 'mul32d', '( %s -> ( %s x. A ) = ( ( 2 x. A ) x. %s ) )' % (A0, TI, I))], 'oveq1d', '( %s -> ( ( %s x. A ) / N ) = ( ( ( 2 x. A ) x. %s ) / N ) )' % (A0, TI, I))
tacn = w.s([two, acn], 'mulcld', '( %s -> ( 2 x. A ) e. CC )' % A0)
e3 = w.s([tacn, icn, ncn, nne], 'div23d', '( %s -> ( ( ( 2 x. A ) x. %s ) / N ) = ( ( ( 2 x. A ) / N ) x. %s ) )' % (A0, I, I))
e4a = w.s([w.s([two, acn], 'mulcomd', '( %s -> ( 2 x. A ) = ( A x. 2 ) )' % A0)], 'oveq1d', '( %s -> ( ( 2 x. A ) / N ) = ( ( A x. 2 ) / N ) )' % A0)
e4b = w.s([acn, two, ncn, nne], 'divassd', '( %s -> ( ( A x. 2 ) / N ) = ( A x. ( 2 / N ) ) )' % A0)
e4 = w.s([w.s([e4a, e4b], 'eqtrd', '( %s -> ( ( 2 x. A ) / N ) = ( A x. ( 2 / N ) ) )' % A0)], 'oveq1d', '( %s -> ( ( ( 2 x. A ) / N ) x. %s ) = ( ( A x. ( 2 / N ) ) x. %s ) )' % (A0, I, I))
e5 = w.s([acn, q, icn], 'mulassd', '( %s -> ( ( A x. ( 2 / N ) ) x. %s ) = ( A x. %s ) )' % (A0, I, Q))
e = w.s([w.s([w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( %s x. ( A / N ) ) = ( ( ( 2 x. A ) x. %s ) / N ) )' % (A0, TI, I)), e3], 'eqtrd', '( %s -> ( %s x. ( A / N ) ) = ( ( ( 2 x. A ) / N ) x. %s ) )' % (A0, TI, I)), e4], 'eqtrd', '( %s -> ( %s x. ( A / N ) ) = ( ( A x. ( 2 / N ) ) x. %s ) )' % (A0, TI, I)), e5], 'eqtrd', '( %s -> ( %s x. ( A / N ) ) = ( A x. %s ) )' % (A0, TI, Q))
lhs = w.s([e], 'fveq2d', '( %s -> %s = ( exp ` ( A x. %s ) ) )' % (A0, E('A'), Q))
w.qed([w.s([lhs, ef], 'eqtrd', '( %s -> %s = ( ( exp ` %s ) ^ A ) )' % (A0, E('A'), Q)), r3], 'eqtr4d', '( %s -> %s = %s )' % (A0, E('A'), RP('A'))); run(w)

# ---- dchrgsval2: root form
Ak = '( %s /\\ a e. %s )' % (HC, FZO('N'))
def term_ef(w, ante, sh=None):
    """under ( ante /\\ a e. ( 0 ..^ N ) ): the exp-form term equals the root-form term"""
    A = '( %s /\\ a e. %s )' % (ante, FZO('N'))
    n = w.s([w.s([], 'simpl', '( %s -> N e. NN )' % HC)] if ante == HC else [w.s([], 'simpl', '( %s -> N e. NN )' % ante)], 'adantr', '( %s -> N e. NN )' % A)
    az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (A, FZO('N')))], 'elfzoelz' if False else 'elfzoelz', '( %s -> a e. ZZ )' % A)
    w.lines.pop()
    az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (A, FZO('N'))), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % A)
    if sh is None:
        arg = 'a'; argz = az
    else:
        arg = '( %s x. a )' % sh
        shz = w.s([w.s([], 'simpr', '( %s -> %s e. ZZ )' % (ante, sh))], 'adantr', '( %s -> %s e. ZZ )' % (A, sh))
        argz = w.s([shz, az], 'zmulcld', '( %s -> %s e. ZZ )' % (A, arg))
    ef = w.s([n, argz, w.inst('dchrgsef')], 'syl2anc', '( %s -> %s = %s )' % (A, E(arg), RP(arg)))
    return w.s([ef], 'oveq2d', '( %s -> %s = %s )' % (A, TERM('X', 'N', 'a', sh), TERMR('X', 'N', 'a', sh)))

w = W('dchrgsval2', 'The Gauss sum in the root-of-unity form: the sum over a in ( 0 ..^ N ) of X at the class of a times ( ( -u 1 ^c ( 2 / N ) ) ^ a ).')
v = w.s([], 'dchrgsval', '( %s -> %s = %s )' % (HC, T, GSBODY('N', 'X')))
te = term_ef(w, HC)
w.qed([v, w.s([te], 'sumeq2dv', '( %s -> %s = %s )' % (HC, GSBODY('N', 'X'), GR('X', 'N', None)))], 'eqtrd', '( %s -> %s = %s )' % (HC, T, GR('X', 'N', None))); run(w)

# ---- dchrgscl
w = W('dchrgscl', 'The Gauss sum is a complex number.')
v = w.s([], 'dchrgsval2', '( %s -> %s = %s )' % (HC, T, GR('X', 'N', None)))
fin = w.s([w.s([], 'fzofi', '%s e. Fin' % FZO('N'))], 'a1i', '( %s -> %s e. Fin )' % (HC, FZO('N')))
g, z, d, l = dchyp(w)
xd = w.s([w.s([], 'simpr', '( %s -> X e. %s )' % (HC, DB('N')))], 'adantr', '( %s -> X e. %s )' % (Ak, DB('N')))
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Ak, FZO('N'))), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Ak)
xc = w.s([g, z, d, l, xd, az], 'dchrzrhcl', '( %s -> %s e. CC )' % (Ak, EV('X', 'N', 'a')))
nn = w.s([w.s([], 'simpl', '( %s -> N e. NN )' % HC)], 'adantr', '( %s -> N e. NN )' % Ak)
rc = w.s([nn, az, w.inst('root1expcl')], 'syl2anc', '( %s -> %s e. CC )' % (Ak, RP('a')))
tc = w.s([xc, rc], 'mulcld', '( %s -> %s e. CC )' % (Ak, TERMR('X', 'N', 'a')))
w.qed([v, w.s([fin, tc], 'fsumcl', '( %s -> %s e. CC )' % (HC, GR('X', 'N', None)))], 'eqeltrd', '( %s -> %s e. CC )' % (HC, T)); run(w)

# ---- dchrgsefsum: the shifted sum in both forms
A0 = '( N e. NN /\\ A e. ZZ )'
w = W('dchrgsefsum', 'The shifted Gauss sum (Mathlib gaussSum chi ( stdAddChar.mulShift A )) in the exp form equals the root-of-unity form.')
te = term_ef(w, A0, 'A')
w.qed([te], 'sumeq2dv', '( %s -> %s = %s )' % (A0, G('X', 'N', 'A'), GR('X', 'N', 'A'))); run(w)

# ---- dchrgsval3: T = GR(X,1)
w = W('dchrgsval3', 'The Gauss sum is the shifted sum at shift 1.')
v = w.s([], 'dchrgsval2', '( %s -> %s = %s )' % (HC, T, GR('X', 'N', None)))
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Ak, FZO('N'))), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Ak)
m = w.s([w.s([w.s([az], 'zcnd', '( %s -> a e. CC )' % Ak)], 'mullidd', '( %s -> ( 1 x. a ) = a )' % Ak)], 'eqcomd', '( %s -> a = ( 1 x. a ) )' % Ak)
t = w.s([w.s([m], 'oveq2d', '( %s -> %s = %s )' % (Ak, RP('a'), RP('( 1 x. a )')))], 'oveq2d', '( %s -> %s = %s )' % (Ak, TERMR('X', 'N', 'a'), TERMR('X', 'N', 'a', '1')))
w.qed([v, w.s([t], 'sumeq2dv', '( %s -> %s = %s )' % (HC, GR('X', 'N', None), GR('X', 'N', '1')))], 'eqtrd', '( %s -> %s = %s )' % (HC, T, GR('X', 'N', '1'))); run(w)
