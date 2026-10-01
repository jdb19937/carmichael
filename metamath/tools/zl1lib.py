"""Sortie ZL1 helpers (Route Z: the L-function interface of a set.mm Dirichlet
character, items (a)-(c) of Z6c-HANDOFF section 8).

STATEMENTS / ORDER are the frozen statements of ZL1-blueprint.md, one place.
`MM_DB=sorties/zl1.mm python3 tools/zl1lib.py [LABEL...]` grammar-checks them.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c5lib import *                       # W, run5, a1, mpv, vexd, HP, BX, TOP, LH, DC, ONE, CHV, ...
from c0lib import hyp, runh
import z6clib as Z6                       # the consumer's macros (z6dlbz)

# ------------------------------------------------------------------ objects
HPZ = HP('0')                              # the open right half-plane
TOPO = '( TopOpen ` CCfld )'
HOL = lambda F, D: '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)
NX = '( N e. NN /\\ X e. %s )' % DC       # a Dirichlet character X mod N
CX = '( a e. NN |-> ( X ` ( %s ` a ) ) )' % LH      # the character read on NN
PRN = Z6.PRN                               # ( n e. NN |-> if ( ( n gcd N ) = 1 , 1 , 0 ) )
QM = 'if ( X = %s , ( ( phi ` N ) / N ) , 0 )' % ONE   # the mean value of the character
CHW = lambda i: '( ( X ` ( %s ` %s ) ) - %s )' % (LH, i, QM)    # the mean-free coefficient
PSW = lambda M, i='i': 'sum_ %s e. ( 1 ... %s ) %s' % (i, M, CHW(i))
WSF = '( q e. NN |-> %s )' % PSW('q')
BW = '( N x. ( 1 + ( abs ` %s ) ) )' % QM
DLT = lambda k, z: '( ( %s ^c -u %s ) - ( ( %s + 1 ) ^c -u %s ) )' % (k, z, k, z)
AB = lambda z, k='k': 'sum_ %s e. NN ( %s x. %s )' % (k, PSW(k), DLT(k, z))
ABF = lambda D=HPZ, z='z': '( %s e. %s |-> %s )' % (z, D, AB(z))
# zeta: HT(k,z) = ( k + z ) ( k + 1 ) ^ -z - k k ^ -z, sum_k HT = ( z - 1 ) zeta ( z ) - z
HT = lambda k, z: '( ( ( %s + %s ) x. ( ( %s + 1 ) ^c -u %s ) ) - ( %s x. ( %s ^c -u %s ) ) )' % (k, z, k, z, k, k, z)
HD = lambda k, z: ('( ( ( ( %s + 1 ) ^c -u %s ) - ( ( %s + %s ) x. ( ( log ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u %s ) ) ) ) + ( %s x. ( ( log ` %s ) x. ( %s ^c -u %s ) ) ) )'
                   % (k, z, k, z, k, k, z, k, k, k, z))            # d/dz HT
HS = lambda z, k='k': 'sum_ %s e. NN %s' % (k, HT(k, z))
ZF = lambda z: '( %s + %s )' % (z, HS(z))                        # ( z - 1 ) zeta ( z ) on Re z > 0
EV = lambda z: '( ( %s x. %s ) + ( ( %s - 1 ) x. %s ) )' % (QM, ZF(z), z, AB(z))
LF = '( N DChrLF X )'
LFM = '( s e. %s |-> %s )' % (HPZ, EV('s'))
# the consumer's interface, instantiated
sub_ = Z6.sub
CI = lambda t: sub_(t, {'C': CX, 'E': LF})
CHRBX = CI(Z6.CHRB)
EHOLX = CI(Z6.EHOL)
RESVX = CI(Z6.RESV)
DSERX = CI(Z6.DSER)
CVXHX = CI(Z6.CVXH)

STATEMENTS = {}
HYPS = {}

# ---------------------------------------------------------------- section A: the character
STATEMENTS['zl1cxv'] = '( ( %s /\\ K e. NN ) -> ( %s ` K ) = ( X ` ( %s ` K ) ) )' % (NX, CX, LH)
STATEMENTS['zl1chrb'] = '( %s -> %s )' % (NX, CHRBX)
STATEMENTS['zl1prn'] = '( %s -> ( %s = %s <-> X = %s ) )' % (NX, CX, PRN, ONE)
STATEMENTS['zl1blk'] = ('( ( %s /\\ J e. NN0 ) -> sum_ i e. ( ( J + 1 ) ... ( J + N ) ) ( X ` ( %s ` i ) ) = if ( X = %s , ( phi ` N ) , 0 ) )'
                        % (NX, LH, ONE))
STATEMENTS['zl1wblk'] = '( ( %s /\\ J e. NN0 ) -> sum_ i e. ( ( J + 1 ) ... ( J + N ) ) %s = 0 )' % (NX, CHW('i'))
STATEMENTS['zl1wper'] = '( ( %s /\\ J e. NN0 ) -> %s = %s )' % (NX, PSW('( J + N )'), PSW('J'))
STATEMENTS['zl1wmod'] = '( ( %s /\\ ( P e. NN0 /\\ Q e. NN0 ) ) -> %s = %s )' % (NX, PSW('( P + ( N x. Q ) )'), PSW('P'))
STATEMENTS['zl1wbnd'] = '( ( %s /\\ M e. NN0 ) -> ( abs ` %s ) <_ %s )' % (NX, PSW('M'), BW)
STATEMENTS['zl1wcsf'] = '( %s -> ( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) )' % (NX, WSF, BW, WSF, BW)
STATEMENTS['zl1ahol'] = '( %s -> %s )' % (NX, HOL(ABF(), HPZ))
STATEMENTS['zl1acl'] = '( ( %s /\\ ( Z e. CC /\\ 0 < ( Re ` Z ) ) ) -> %s e. CC )' % (NX, AB('Z'))
STATEMENTS['zl1aagr'] = ('( ( %s /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) -> %s = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )'
                         % (NX, AB('Z'), CHW('k')))

# ---------------------------------------------------------------- section B: ( s - 1 ) zeta ( s )
IOO = '( K (,) ( K + 1 ) )'
STATEMENTS['zl1lip'] = ('( ( ( F : RR+ --> CC /\\ G : RR+ --> CC /\\ ( RR _D F ) = G ) /\\ ( K e. RR+ /\\ M e. RR /\\ '
                        'A. t e. %s ( abs ` ( G ` t ) ) <_ M ) ) -> ( abs ` ( ( F ` ( K + 1 ) ) - ( F ` K ) ) ) <_ M )' % IOO)
# the primitive F ( b ) = ( Z - 1 ) K b ^ -Z - Z b ^ ( 1 - Z ), F ( K ) - F ( K + 1 ) = HT ( K , Z )
FB = lambda b: '( ( ( ( Z - 1 ) x. K ) x. ( %s ^c -u Z ) ) - ( Z x. ( %s ^c ( 1 - Z ) ) ) )' % (b, b)
FD = lambda b: '( ( Z x. ( Z - 1 ) ) x. ( ( %s - K ) x. ( %s ^c ( -u Z - 1 ) ) ) )' % (b, b)
FM = '( b e. RR+ |-> %s )' % FB('b')
FDM = '( b e. RR+ |-> %s )' % FD('b')
STATEMENTS['zl1fdv'] = '( ( K e. RR /\\ Z e. CC ) -> ( RR _D %s ) = %s )' % (FM, FDM)
MV = '( ( ( abs ` Z ) x. ( abs ` ( Z - 1 ) ) ) x. ( K ^c ( -u ( Re ` Z ) - 1 ) ) )'
STATEMENTS['zl1hvb'] = '( ( ( K e. NN /\\ Z e. CC ) /\\ 0 < ( Re ` Z ) ) -> ( abs ` %s ) <_ %s )' % (HT('K', 'Z'), MV)
# the z-derivative P ( b ) = K b ^ -Z - b ^ ( 1 - Z ) - log b F ( b ), P ( K ) - P ( K + 1 ) = HD ( K , Z )
PB = lambda b: '( ( ( K x. ( %s ^c -u Z ) ) - ( %s ^c ( 1 - Z ) ) ) - ( ( log ` %s ) x. %s ) )' % (b, b, b, FB(b))
PD = lambda b: '( ( ( %s - K ) x. ( %s ^c ( -u Z - 1 ) ) ) x. ( ( ( 2 x. Z ) - 1 ) - ( ( Z x. ( Z - 1 ) ) x. ( log ` %s ) ) ) )' % (b, b, b)
PM = '( b e. RR+ |-> %s )' % PB('b')
PDM = '( b e. RR+ |-> %s )' % PD('b')
STATEMENTS['zl1pdv'] = '( ( K e. RR /\\ Z e. CC ) -> ( RR _D %s ) = %s )' % (PM, PDM)
MD = '( ( ( abs ` ( ( 2 x. Z ) - 1 ) ) + ( ( ( abs ` Z ) x. ( abs ` ( Z - 1 ) ) ) x. ( log ` ( K + 1 ) ) ) ) x. ( K ^c ( -u ( Re ` Z ) - 1 ) ) )'
STATEMENTS['zl1hdb'] = '( ( ( K e. NN /\\ Z e. CC ) /\\ 0 < ( Re ` Z ) ) -> ( abs ` %s ) <_ %s )' % (HD('K', 'Z'), MD)
STATEMENTS['zl1hdv'] = '( ( K e. NN /\\ U e. %s ) -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (TOPO, HT('K', 'z'), HD('K', 'z'))
STATEMENTS['zl1hthol'] = '( ( K e. NN /\\ U e. %s ) -> %s )' % (TOPO, HOL('( z e. U |-> %s )' % HT('K', 'z'), 'U'))
# the UH package on the open box BX ( L , R ) (C5's abbxuh)
B_ = BX()
HTF = '( a e. NN |-> ( p e. %s |-> %s ) )' % (B_, HT('a', 'p'))
EL = '( L / 2 )'
C1 = '( ( 2 x. R ) x. ( ( 2 x. R ) + 1 ) )'
MAJZ = '( n e. NN |-> ( %s x. ( n ^c -u ( L + 1 ) ) ) )' % C1
C2 = '( ( ( 4 x. R ) + 1 ) + ( %s x. ( ( 2 ^c %s ) / %s ) ) )' % (C1, EL, EL)
MAJZD = '( n e. NN |-> ( %s x. ( n ^c -u ( 1 + %s ) ) ) )' % (C2, EL)


def UHZ(F=HTF, M=MAJZ, R_=MAJZD, U=B_):
    return UH(F, M, R_, U)


STATEMENTS['zl1zuh'] = '( ( L e. RR+ /\\ R e. RR ) -> %s )' % UHZ()
STATEMENTS['zl1zbx'] = '( ( L e. RR+ /\\ R e. RR ) -> %s )' % HOL('( z e. %s |-> %s )' % (B_, HS('z')), B_)
STATEMENTS['zl1zhol'] = HOL('( z e. %s |-> %s )' % (HPZ, HS('z')), HPZ)
STATEMENTS['zl1zcl'] = '( ( Z e. CC /\\ 0 < ( Re ` Z ) ) -> %s e. CC )' % HS('Z')
EZ = lambda n: '( ( %s + Z ) x. ( ( %s + 1 ) ^c -u Z ) )' % (n, n)
STATEMENTS['zl1ztel'] = ('( ( Z e. CC /\\ M e. NN ) -> ( Z + sum_ k e. ( 1 ... M ) %s ) = ( ( ( Z - 1 ) x. sum_ k e. ( 1 ... M ) ( k ^c -u Z ) ) + %s ) )'
                         % (HT('k', 'Z'), EZ('M')))
STATEMENTS['zl1zlim0'] = '( ( Z e. CC /\\ 1 < ( Re ` Z ) ) -> ( n e. NN |-> %s ) ~~> 0 )' % EZ('n')
STATEMENTS['zl1zser'] = '( ( Z e. CC /\\ 1 < ( Re ` Z ) ) -> %s = ( ( Z - 1 ) x. sum_ k e. NN ( k ^c -u Z ) ) )' % ZF('Z')
STATEMENTS['zl1z1'] = '%s = 0' % HS('1')

# convergence and box bounds (helpers of zl1zuh / zl1zhol / zl1zser)
STATEMENTS['zl1zcv'] = '( ( Z e. CC /\\ 0 < ( Re ` Z ) ) -> seq 1 ( + , ( m e. NN |-> %s ) ) e. dom ~~> )' % HT('m', 'Z')
BXH = '( ( L e. RR+ /\\ R e. RR ) /\\ Z e. %s )' % B_
STATEMENTS['zl1hvbx'] = '( ( K e. NN /\\ %s ) -> ( abs ` %s ) <_ ( %s x. ( K ^c -u ( L + 1 ) ) ) )' % (BXH, HT('K', 'Z'), C1)
STATEMENTS['zl1hdbx'] = '( ( K e. NN /\\ %s ) -> ( abs ` %s ) <_ ( %s x. ( K ^c -u ( 1 + %s ) ) ) )' % (BXH, HD('K', 'Z'), C2, EL)
# the ring identities (closed complex algebra, one per derivative / value computation)
STATEMENTS['zl1alg1'] = ('( ( ( Z e. CC /\\ K e. CC ) /\\ ( B e. CC /\\ P e. CC ) ) -> ( ( ( ( Z - 1 ) x. K ) x. ( -u Z x. P ) ) - '
                         '( Z x. ( ( 1 - Z ) x. ( P x. B ) ) ) ) = ( ( Z x. ( Z - 1 ) ) x. ( ( B - K ) x. P ) ) )')
STATEMENTS['zl1alg2'] = ('( ( ( Z e. CC /\\ K e. CC ) /\\ ( P e. CC /\\ Q e. CC ) ) -> ( ( ( ( ( Z - 1 ) x. K ) x. P ) - ( Z x. ( P x. K ) ) ) = -u ( K x. P ) /\\ '
                         '( ( ( ( Z - 1 ) x. K ) x. Q ) - ( Z x. ( Q x. ( K + 1 ) ) ) ) = -u ( ( K + Z ) x. Q ) ) )')
_FBP = '( ( ( ( Z - 1 ) x. K ) x. ( P x. B ) ) - ( Z x. ( ( P x. B ) x. B ) ) )'
STATEMENTS['zl1alg3'] = ('( ( ( ( Z e. CC /\\ K e. CC ) /\\ ( B e. CC /\\ B =/= 0 ) ) /\\ ( P e. CC /\\ L e. CC ) ) -> '
                         '( ( ( K x. ( -u Z x. P ) ) - ( ( 1 - Z ) x. ( P x. B ) ) ) - ( ( ( 1 / B ) x. %s ) + '
                         '( ( ( Z x. ( Z - 1 ) ) x. ( ( B - K ) x. P ) ) x. L ) ) ) = '
                         '( ( ( B - K ) x. P ) x. ( ( ( 2 x. Z ) - 1 ) - ( ( Z x. ( Z - 1 ) ) x. L ) ) ) )' % _FBP)
STATEMENTS['zl1alg4'] = ('( ( ( ( Z e. CC /\\ K e. CC ) /\\ ( P e. CC /\\ Q e. CC ) ) /\\ ( A e. CC /\\ G e. CC ) ) -> '
                         '( ( ( ( K x. P ) - ( P x. K ) ) - ( A x. -u ( K x. P ) ) ) - '
                         '( ( ( K x. Q ) - ( Q x. ( K + 1 ) ) ) - ( G x. -u ( ( K + Z ) x. Q ) ) ) ) = '
                         '( ( Q - ( ( K + Z ) x. ( G x. Q ) ) ) + ( K x. ( A x. P ) ) ) )')
STATEMENTS['zl1alg5'] = ('( ( ( Z e. CC /\\ K e. CC ) /\\ ( ( P e. CC /\\ Q e. CC ) /\\ ( A e. CC /\\ G e. CC ) ) ) -> '
                         '( ( ( 1 x. Q ) + ( -u ( G x. Q ) x. ( K + Z ) ) ) - ( K x. -u ( A x. P ) ) ) = '
                         '( ( Q - ( ( K + Z ) x. ( G x. Q ) ) ) + ( K x. ( A x. P ) ) ) )')

# ---------------------------------------------------------------- section C: the interface
STATEMENTS['zl1hcomb'] = ('( ( %s /\\ %s /\\ C e. CC ) -> %s )'
                          % (HOL('F', 'D'), HOL('G', 'D'),
                             HOL('( z e. D |-> ( ( C x. ( z + ( F ` z ) ) ) + ( ( z - 1 ) x. ( G ` z ) ) ) )', 'D')))
STATEMENTS['dchrlfval'] = '( %s -> %s = %s )' % (NX, LF, LFM)
STATEMENTS['zl1ehol'] = '( %s -> %s )' % (NX, HOL(LF, HPZ))
STATEMENTS['zl1e1'] = '( %s -> ( %s ` 1 ) = %s )' % (NX, LF, RESVX)
STATEMENTS['zl1dser'] = '( %s -> %s )' % (NX, DSERX)
STATEMENTS['zl1lif'] = '( %s -> ( %s /\\ ( ( %s /\\ ( %s ` 1 ) = %s ) /\\ %s ) ) )' % (NX, CHRBX, EHOLX, LF, RESVX, DSERX)
# z6dlbz at the character: everything but CVXH discharged
ZA = ('( ( ( %s /\\ %s ) /\\ ( ( ( %s /\\ S =/= 1 ) /\\ %s ) /\\ ( %s /\\ ( %s /\\ ( %s ` S ) = 0 ) ) ) ) /\\ ( %s /\\ ( %s = %s -> %s <_ ( abs ` ( Im ` S ) ) ) ) )'
      % (Z6.HZD3, NX, Z6.SRNG, Z6.HDN, Z6.T1, CVXHX, LF, Z6.TRNG, CX, PRN, Z6.LAM60))
STATEMENTS['zl1dlbz'] = ('( %s -> ( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ ( abs ` %s ) )'
                         % (ZA, CI(Z6.FDV)))

ALG = ['zl1alg1', 'zl1alg2', 'zl1alg3', 'zl1alg4', 'zl1alg5']
ORDER = ALG + ['zl1cxv', 'zl1chrb', 'zl1prn', 'zl1blk', 'zl1wblk', 'zl1wper', 'zl1wmod', 'zl1wbnd', 'zl1wcsf', 'zl1ahol', 'zl1acl', 'zl1aagr',
         'zl1lip', 'zl1fdv', 'zl1hvb', 'zl1pdv', 'zl1hdb', 'zl1hdv', 'zl1hthol', 'zl1zcv', 'zl1hvbx', 'zl1hdbx', 'zl1zuh', 'zl1zbx', 'zl1zhol', 'zl1zcl', 'zl1ztel', 'zl1zlim0', 'zl1zser', 'zl1z1',
         'zl1hcomb', 'dchrlfval', 'zl1ehol', 'zl1e1', 'zl1dser', 'zl1lif', 'zl1dlbz']


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('zl1g' + lab, 'grammar check of %s' % lab)
        for n, f in HYPS.get(lab, []):
            hyp(w, n, '%s.%s' % (lab, n), f)
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


def run(w):
    return (runh if HYPS.get(w.label) else (lambda x: x.run()))(w)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])


# ------------------------------------------------------------------ step helpers
def chain(w, ante, terms, steps, name=None):
    """( ante -> t0 = tn ) from steps[i]: ( ante -> t_i = t_(i+1) ) (a step name, or
    ('r', name) for a step proving t_(i+1) = t_i)"""
    cur = None
    for i, st in enumerate(steps):
        a, b = terms[i], terms[i + 1]
        if isinstance(st, tuple):
            st = w.s([st[1]], 'eqcomd', '( %s -> %s = %s )' % (ante, a, b))
        if cur is None:
            cur = st
        else:
            last = i == len(steps) - 1
            cur = w.s([cur, st], 'eqtrd', '( %s -> %s = %s )' % (ante, terms[0], b), name=(name if last else None))
    return cur


def d(w, ante, ref, hyps, concl):
    """deduction step ( ante -> concl )"""
    return w.s(hyps, ref, '( %s -> %s )' % (ante, concl))


def cl2(w, ante, ref, a, b, sa, sb, op):
    return w.s([sa, sb], ref, '( %s -> ( %s %s %s ) e. CC )' % (ante, a, op, b))


# ------------------------------------------------------------------ power rewriting (zl1_hv, zl1_hd)
RZ = '( Re ` Z )'
NZ1 = '( -u Z - 1 )'
ZK = '( ( Z - 1 ) x. K )'


def E(w, ante, ref, hyps, l, r):
    return w.s(hyps, ref, '( %s -> %s = %s )' % (ante, l, r))




def pw1(w, ante, b, bc, bne, zc):
    """( ante -> ( b ^c ( ( 1 - Z ) - 1 ) ) = ( ( b ^c ( -u Z - 1 ) ) x. b ) ) and the exponent identity"""
    c1 = a1(w, ante, 'ax-1cn', '1 e. CC')
    e1 = E(w, ante, 'sub32d', [c1, zc, c1], '( ( 1 - Z ) - 1 )', '( ( 1 - 1 ) - Z )')
    e2 = E(w, ante, 'oveq1d', [E(w, ante, 'subidd', [c1], '( 1 - 1 )', '0')], '( ( 1 - 1 ) - Z )', '( 0 - Z )')
    e3 = w.s([w.s([w.s([], 'df-neg', '-u Z = ( 0 - Z )')], 'eqcomi', '( 0 - Z ) = -u Z')], 'a1i', '( %s -> ( 0 - Z ) = -u Z )' % ante)
    nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % ante)
    e4 = E(w, ante, 'npcand', [nzc, c1], '( %s + 1 )' % NZ1, '-u Z')
    ex = chain(w, ante, ['( ( 1 - Z ) - 1 )', '( ( 1 - 1 ) - Z )', '( 0 - Z )', '-u Z', '( %s + 1 )' % NZ1], [e1, e2, e3, ('r', e4)])
    e5 = E(w, ante, 'oveq2d', [ex], '( %s ^c ( ( 1 - Z ) - 1 ) )' % b, '( %s ^c ( %s + 1 ) )' % (b, NZ1))
    nz1 = w.s([nzc, c1], 'subcld', '( %s -> %s e. CC )' % (ante, NZ1))
    e6 = w.s([bc, bne, nz1, w.inst('cxpp1')], 'syl3anc', '( %s -> ( %s ^c ( %s + 1 ) ) = ( ( %s ^c %s ) x. %s ) )' % (ante, b, NZ1, b, NZ1, b))
    return chain(w, ante, ['( %s ^c ( ( 1 - Z ) - 1 ) )' % b, '( %s ^c ( %s + 1 ) )' % (b, NZ1), '( ( %s ^c %s ) x. %s )' % (b, NZ1, b)], [e5, e6])


def pwm(w, ante, b, bc, bne, zc):
    """( ante -> ( b ^c ( 1 - Z ) ) = ( ( b ^c -u Z ) x. b ) )"""
    c1 = a1(w, ante, 'ax-1cn', '1 e. CC')
    nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % ante)
    e1 = E(w, ante, 'addcomd', [nzc, c1], '( -u Z + 1 )', '( 1 + -u Z )')
    e2 = E(w, ante, 'negsubd', [c1, zc], '( 1 + -u Z )', '( 1 - Z )')
    ex = chain(w, ante, ['( 1 - Z )', '( 1 + -u Z )', '( -u Z + 1 )'], [('r', e2), ('r', e1)])
    e3 = E(w, ante, 'oveq2d', [ex], '( %s ^c ( 1 - Z ) )' % b, '( %s ^c ( -u Z + 1 ) )' % b)
    e4 = w.s([bc, bne, nzc, w.inst('cxpp1')], 'syl3anc', '( %s -> ( %s ^c ( -u Z + 1 ) ) = ( ( %s ^c -u Z ) x. %s ) )' % (ante, b, b, b))
    return chain(w, ante, ['( %s ^c ( 1 - Z ) )' % b, '( %s ^c ( -u Z + 1 ) )' % b, '( ( %s ^c -u Z ) x. %s )' % (b, b)], [e3, e4])



from cl import Closure


def dvF(w, A0, zc, kc):
    """( A0 -> ( RR _D FM ) = ( b e. RR+ |-> ( ( ZK x. ( -u Z x. b^(-Z-1) ) ) - ( Z x. ( ( 1 - Z ) x. b^((1-Z)-1) ) ) ) ) )"""
    sr = a1(w, A0, 'prid1', 'RR e. { RR , CC }')
    Ab = '( %s /\\ b e. RR+ )' % A0
    brp = w.s([], 'simpr', '( %s -> b e. RR+ )' % Ab)
    c = Closure(w, Ab, {'b': ('RR+', brp), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ab)),
                        'K': ('CC', w.s([kc], 'adantr', '( %s -> K e. CC )' % Ab))})
    m = lambda e: c.mem(e, 'CC')
    nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0)
    omz = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), zc], 'subcld', '( %s -> ( 1 - Z ) e. CC )' % A0)
    D1 = '( -u Z x. ( b ^c ( -u Z - 1 ) ) )'
    D2 = '( ( 1 - Z ) x. ( b ^c ( ( 1 - Z ) - 1 ) ) )'
    d1 = w.s([nzc, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( b e. RR+ |-> ( b ^c -u Z ) ) ) = ( b e. RR+ |-> %s ) )' % (A0, D1))
    d2 = w.s([omz, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( b e. RR+ |-> ( b ^c ( 1 - Z ) ) ) ) = ( b e. RR+ |-> %s ) )' % (A0, D2))
    zkc = w.s([w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0), kc], 'mulcld', '( %s -> %s e. CC )' % (A0, ZK))
    d3 = w.s([sr, m('( b ^c -u Z )'), m(D1), d1, zkc], 'dvmptcmul',
             '( %s -> ( RR _D ( b e. RR+ |-> ( %s x. ( b ^c -u Z ) ) ) ) = ( b e. RR+ |-> ( %s x. %s ) ) )' % (A0, ZK, ZK, D1))
    d4 = w.s([sr, m('( b ^c ( 1 - Z ) )'), m(D2), d2, zc], 'dvmptcmul',
             '( %s -> ( RR _D ( b e. RR+ |-> ( Z x. ( b ^c ( 1 - Z ) ) ) ) ) = ( b e. RR+ |-> ( Z x. %s ) ) )' % (A0, D2))
    RHS = '( ( %s x. %s ) - ( Z x. %s ) )' % (ZK, D1, D2)
    d5 = w.s([sr, m('( %s x. ( b ^c -u Z ) )' % ZK), m('( %s x. %s )' % (ZK, D1)), d3, m('( Z x. ( b ^c ( 1 - Z ) ) )'), m('( Z x. %s )' % D2), d4],
             'dvmptsub', '( %s -> ( RR _D %s ) = ( b e. RR+ |-> %s ) )' % (A0, FM, RHS))
    return d5, RHS, Ab, brp, c




def selfv(w, A0, x, X, body, mp, cls):
    """( ( A0 /\\ x e. X ) -> ( mp ` x ) = body ) for mp = ( x e. X |-> body ), from
    cls: ( ( A0 /\\ x e. X ) -> body e. CC )  (fvmpt2d: the argument is the binder)"""
    e = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, mp, mp))
    return w.s([e, cls], 'fvmpt2d', '( ( %s /\\ %s e. %s ) -> ( %s ` %s ) = %s )' % (A0, x, X, mp, x, body))


def mptv(w, ante, x, X, body, T, mem, mp=None, exs=None, closure=None):
    """congr.mptval without its dummy-variable lint (fvmptg's proof dummy y is not a
    restriction on its users: TOOLING-DEBT item 3); returns (step, value)"""
    from congr import congruence, StepGen, _vexd
    mp = mp or '( %s e. %s |-> %s )' % (x, X, body)
    eq = '%s = %s' % (x, T)
    g = w.g
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, val = congruence(body, {x: T}, eq, {x: idx}, g)
    w.lines.extend(g.lines); g.lines = []
    if st is None:
        st = w.s([], 'eqidd', '( %s -> %s = %s )' % (eq, body, val))
    em = w.s([], 'eqid', '%s = %s' % (mp, mp))
    fm = w.s([st, em], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (T, X, val, mp, T, val))
    ex = _vexd(w, ante, val, closure, exs)
    return w.s([mem, ex, fm], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, T, val)), val


def mptval_(w, *a, **k):
    """congr.mptval with the worksheet's own step generator (unique step names)"""
    from congr import mptval as _mv
    k.setdefault('gen', w.g)
    r = _mv(w, *a, **k)
    w.lines.extend(w.g.lines); w.g.lines = []
    return r
