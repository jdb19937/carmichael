"""Sortie LD2 helpers (Route Z: LoggedDetector.lean 1350-2021, the second half; completes the file).

STATEMENTS / HYPS / ORDER are the frozen statements of LD2-HANDOFF.md, one place;
`MM_DB=sorties/ld2.mm python3 tools/ld2lib.py [LABEL...]` grammar-checks them through mmatch.

Objects (written-out classes, no df-; LD1's and DSH's macros are imported):
  ECTRH               = EctrHalf chi D (Ypar D) rho at the interface class E and the character function C
  CX(X)               = ( a e. NN |-> ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) ) )   (the values of a set.mm character)
  LFX(X)              = ( N DChrLF X )                                             (its L-function, ZL1)
  ECTRHX(X, S)        = ECTRH at E := LFX(X), C := CX(X), the point S               (LDEN's EctrHalf (chi r) D (Ypar D) (rho r))
  TWISTX(j, k, G, T)  = twistSum D T j k X G  (LD1's TWIST with the character value written out)
  HLU(U) = HL + i U, GRHV(U) = ( GRH ` HLU(U) ) (the contour integrand on the half line), MRU(U), MA(U) = abs Mr ( S + HLU(U) )
  WT(U) = e^-(|U|/2), WT4(U) = e^-(|U|/4), WTA(A, U) = e^-(A |U|)
  KC = 576 10^8 CTau D^(201/800) log D YP^(1/2 - T)  (Lean Kcls with the Gamma constant 12000 for 201 C_Gamma)
  LIH(H) = the truncated line integral to height H, VLH = its limit (the VL of ECTRH), IOH(H) = ( -H (,) H )
  AF = ( d e. NN |-> bvLam(d) d^-1/2 ), M2D = |_ 2 D, DSX(X, G) = MV's DS with the coefficients AF
  BV = KC^2 51200 D log^3 D, FINAL = 10^25 CTau^2 log^5 D D^((151/50)(1 - T))
Letters: sums bind n (integers), m (block), k (Taylor index), r (family), d (AF); a b in the family quantifiers
and CX; u the integration variable; t w inside VL / GRH; s p k in LIF.  Class variables: D N C S T (sigma)
E X (a character) F (the family) K (its characters) Y (its points) V (the height) H (a truncation height)
U (a real) A B W Z M.
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ld1lib import (YP, NMAX, JPAR, BLK, COEFF, HL, HZH, SRNGH, FDVH, EPH, ECTRH, A7H, PRN, HAB0, CFN, CB,
                    LOGD, HZ2, HDN, CVXH, NEX, TWIST, TAYSUM, BLKSUM, TRUNC, V4, V8, KHALF, SIG, HB, HA, BVA, EXY,
                    STATEMENTS as LD1S)
from dshlib import GRH, TPI
import z6alib as Z6
from z6alib import LIF, CHRB, EHOL, DSER, RESV, VL, VLF, LI, HPZ, DG
from mvlib import DB, LZ, CHV, ABS2, IOO, ITG

STATEMENTS = {}
HYPS = {}
ORDER = []


def st(label, text, hyps=()):
    STATEMENTS[label] = ' '.join(text.split())
    HYPS[label] = list(hyps)
    ORDER.append(label)


def subst(text, m):
    """token substitution of class variables"""
    return ' '.join(m.get(t, t) for t in text.split())


# ------------------------------------------------------------------ characters
CX = lambda X='X': '( a e. NN |-> %s )' % CHV(X, 'a')
LFX = lambda X='X': '( N DChrLF %s )' % X
ZG = '( 0g ` ( DChr ` N ) )'
ECTRHX = lambda X='X', S='S': subst(ECTRH, {'S': S, 'E': LFX(X), 'C': CX(X)})
TSX = lambda j, k, n, G, T='T', X='X': '( ( %s x. %s ) x. %s )' % (COEFF(j, k, n, T), CHV(X, n), NEX(n, G))
TWISTX = lambda j, k, G, T='T', X='X': 'sum_ n e. %s %s' % (BLK(j), TSX(j, k, 'n', G, T, X))
assert subst(TWIST('m', 'k', '( Im ` S )'), {'C': CX()}) != TWISTX('m', 'k', '( Im ` S )')   # CX ` n is not CHV ( n ): ld2dlvx rewrites it

# ------------------------------------------------------------------ section 5 (L1.e): the hypotheses
AIS = '( abs ` ( Im ` S ) )'
HTC = '( C = %s -> %s <_ %s )' % (PRN, LOGD, AIS)                      # the principal-character height clause
HDLV = ('( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( ( S e. CC /\\ ( T e. RR /\\ %s ) ) /\\ S =/= 1 ) ) ) /\\ ( %s /\\ ( %s /\\ ( E ` S ) = 0 ) ) )'
        % (HZH, CHRB, SIG, HTC, LIF))
EXH = '( exp ` ( -u 1 / %s ) )' % YP
ECS = '( abs ` %s ) < ( 1 / 4 )' % ECTRH

st('ld2exp', '( %s -> ( 3 / 4 ) <_ %s )' % (HZH, EXH))
st('ld2epb', '( ( ( %s /\\ N e. NN ) /\\ ( ( C : NN --> CC /\\ %s ) /\\ %s ) ) -> ( abs ` %s ) <_ ( 1 / 8 ) )' % (HZH, SRNGH, HTC, EPH('C')))
st('ld2fdv', '( ( %s /\\ %s ) -> ( 3 / 8 ) <_ ( abs ` %s ) )' % (HDLV, ECS, FDVH))
st('ld2trl', '( ( %s /\\ %s ) -> ( 1 / 4 ) <_ ( abs ` %s ) )' % (HDLV, ECS, TRUNC))
EXMK = lambda body: 'E. m e. ( 0 ..^ %s ) E. k e. ( 0 ... %s ) %s <_ ( abs ` %s )' % (JPAR, JPAR, V8, body)
st('ld2dlv', '( %s -> ( ( 1 / 4 ) <_ ( abs ` %s ) \\/ %s ) )' % (HDLV, ECTRH, EXMK(TWIST('m', 'k', '( Im ` S )'))))
HTX = '( X = %s -> %s <_ %s )' % (ZG, LOGD, AIS)
HDLVX = ('( ( ( %s /\\ N e. NN ) /\\ ( X e. %s /\\ ( ( S e. CC /\\ S =/= 1 ) /\\ ( T e. RR /\\ %s ) ) ) ) /\\ ( %s /\\ ( %s ` S ) = 0 ) )'
         % (HZH, DB(), SIG, HTX, LFX()))
st('ld2dlvx', '( %s -> ( ( 1 / 4 ) <_ ( abs ` %s ) \\/ %s ) )' % (HDLVX, ECTRHX(), EXMK(TWISTX('m', 'k', '( Im ` S )'))))

# ------------------------------------------------------------------ section 6 (L1.f): objects
A7C = '( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( %s /\\ S =/= 1 ) ) ) /\\ ( %s /\\ ( E ` S ) = 0 ) )' % (HZH, CFN, SRNGH, LIF)
HP6 = '( %s /\\ ( %s /\\ ( T e. RR /\\ ( ( ; 3 9 / ; 5 0 ) <_ T /\\ T <_ ( Re ` S ) ) ) ) )' % (A7C, HDN)
HLU = lambda U: '( %s + ( _i x. %s ) )' % (HL, U)
GRHV = lambda U: '( %s ` %s )' % (GRH, HLU(U))
MRF = '( <. D , ( 2 x. D ) >. Mr <. C , 1 >. )'
MRU = lambda U: '( %s ` ( S + %s ) )' % (MRF, HLU(U))
MA = lambda U: '( abs ` %s )' % MRU(U)
WTA = lambda A, U: '( exp ` -u ( %s x. ( abs ` %s ) ) )' % (A, U)
WT = lambda U: WTA('( 1 / 2 )', U)
WT4 = lambda U: WTA('( 1 / 4 )', U)
P8 = '( ; 1 0 ^ 8 )'
YPT = '( %s ^c ( ( 1 / 2 ) - T ) )' % YP
KC = '( ( ( ( ; ; 5 7 6 x. %s ) x. CTau ) x. ( D ^c ( ; ; 2 0 1 / ; ; 8 0 0 ) ) ) x. ( %s x. %s ) )' % (P8, LOGD, YPT)
LIH = lambda H: LI(GRH, HL, H)
VLH = VL(GRH, HL)
VLFH = VLF(GRH, HL)
assert ECTRH == '( ( 1 / %s ) x. %s )' % (TPI, VLH)
IOH = lambda H: IOO('-u %s' % H, H)
GAMC = '; ; ; ; 1 2 0 0 0'
LOG3 = '( D x. ( ( log ` D ) ^ 3 ) )'
BV = '( ( %s ^ 2 ) x. ( ; ; ; ; 5 1 2 0 0 x. %s ) )' % (KC, LOG3)
M2D = '( |_ ` ( 2 x. D ) )'
AF = '( d e. NN |-> ( ( ( D bvLam ( 2 x. D ) ) ` d ) x. ( d ^c -u ( 1 / 2 ) ) ) )'
DSX = lambda X, G, n='n': 'sum_ %s e. ( 1 ... %s ) ( ( ( %s ` %s ) x. %s ) x. %s )' % (n, M2D, AF, n, CHV(X, n), NEX(n, G))
SLA = 'sum_ n e. ( 1 ... %s ) ( ( 1 + ( ( log ` n ) ^ 2 ) ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) ) )' % (M2D, AF)
SLA = 'sum_ n e. ( 1 ... %s ) ( ( 1 + ( ( log ` n ) ^ 2 ) ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) )' % (M2D, AF)
EXP2 = '( ( ; ; 1 5 1 / ; 5 0 ) x. ( 1 - T ) )'
FINAL = '( ( ( ( ; 1 0 ^ ; 2 5 ) x. ( CTau ^ 2 ) ) x. ( ( log ` D ) ^ 5 ) ) x. ( D ^c %s ) )' % EXP2

# the family (Lean: s, chi, rho with hrho and hsep; D = d ( t + 2 ), 2 <= t; plus the two carried deviations)
PTS = ('A. a e. F ( ( T <_ ( Re ` ( Y ` a ) ) /\\ ( Re ` ( Y ` a ) ) <_ 1 ) /\\ ( ( abs ` ( Im ` ( Y ` a ) ) ) <_ V /\\ '
       '( ( Y ` a ) =/= 1 /\\ ( ( N DChrLF ( K ` a ) ) ` ( Y ` a ) ) = 0 ) ) )')
SEPY = ('A. a e. F A. b e. F ( ( a =/= b /\\ ( K ` a ) = ( K ` b ) ) -> 1 <_ ( abs ` ( ( Im ` ( Y ` a ) ) - ( Im ` ( Y ` b ) ) ) ) )')
HFAM = ('( ( ( %s /\\ ( N e. NN /\\ V e. RR ) ) /\\ ( 2 <_ V /\\ D = ( N x. ( V + 2 ) ) ) ) /\\ '
        '( ( T e. RR /\\ ( ( ; 3 9 / ; 5 0 ) <_ T /\\ T <_ 1 ) ) /\\ ( ( F e. Fin /\\ K : F --> %s /\\ Y : F --> CC ) /\\ ( %s /\\ %s ) ) ) )'
        % (HZH, DB(), PTS, SEPY))
# the per-member objects at an index Z of the family
KZ = lambda Z: '( K ` %s )' % Z
YZ = lambda Z: '( Y ` %s )' % Z
FAM = lambda Z: {'S': YZ(Z), 'C': CX(KZ(Z)), 'E': LFX(KZ(Z))}
MAK = lambda Z, U: subst(MA(U), FAM(Z))
LIK = lambda Z, H: subst(LIH(H), FAM(Z))
VLK = lambda Z: subst(VLH, FAM(Z))
ECTRK = lambda Z: ECTRHX(KZ(Z), YZ(Z))
assert ECTRK('r') == subst(ECTRH, FAM('r'))
HP6K = lambda Z: subst(HP6, FAM(Z))

# ------------------------------------------------------------------ section 6: the statements
st('ld2gam', '( ( W e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ -u ( 7 / ; 2 5 ) ) ) -> '
   '( abs ` ( _G ` W ) ) <_ ( %s x. ( exp ` -u ( abs ` ( Im ` W ) ) ) ) )' % GAMC)
st('ld2wsq', '( ( X e. RR /\\ 0 <_ X ) -> ( ( ( 1 + X ) ^ 2 ) x. ( exp ` -u X ) ) <_ ( 8 x. ( exp ` -u ( ( 1 / 2 ) x. X ) ) ) )')
st('ld2wlin', '( ( X e. RR /\\ 0 <_ X ) -> ( ( 3 + X ) x. ( exp ` -u ( ( 1 / 2 ) x. X ) ) ) <_ ( 4 x. ( exp ` -u ( ( 1 / 4 ) x. X ) ) ) )')
st('ld2wtcn', '( A e. RR -> ( u e. RR |-> %s ) e. ( RR -cn-> CC ) )' % WTA('A', 'u'))
st('ld2rribl', '( ph -> ( u e. ( A (,) B ) |-> X ) e. L^1 )',
   [('1', '( ph -> ( A e. RR /\\ B e. RR ) )'), ('2', '( ph -> ( u e. RR |-> X ) e. ( RR -cn-> CC ) )')])
st('ld2efitg', '( ( A e. RR+ /\\ ( B e. RR /\\ 0 <_ B ) ) -> %s <_ ( 1 / A ) )' % ITG(IOO('0', 'B'), '( exp ` -u ( A x. u ) )', 'u'))
st('ld2wint', '( ( A e. RR+ /\\ H e. RR+ ) -> %s <_ ( 2 / A ) )' % ITG(IOH('H'), WTA('A', 'u'), 'u'))
IAB = IOO('A', 'B')
st('ld2cs', '( ph -> ( ( 2 x. ( X x. M ) ) x. %s ) <_ ( ( ( X ^ 2 ) x. %s ) + ( ( M ^ 2 ) x. %s ) ) )'
   % (ITG(IAB, '( W x. Z )', 'u'), ITG(IAB, 'W', 'u'), ITG(IAB, '( W x. ( Z ^ 2 ) )', 'u')),
   [('1', '( ph -> ( A e. RR /\\ B e. RR ) )'),
    ('2', '( ( ph /\\ u e. %s ) -> ( W e. RR /\\ 0 <_ W ) )' % IAB),
    ('3', '( ( ph /\\ u e. %s ) -> ( Z e. RR /\\ 0 <_ Z ) )' % IAB),
    ('4', '( ph -> ( u e. %s |-> W ) e. L^1 )' % IAB),
    ('5', '( ph -> ( u e. %s |-> ( W x. Z ) ) e. L^1 )' % IAB),
    ('6', '( ph -> ( u e. %s |-> ( W x. ( Z ^ 2 ) ) ) e. L^1 )' % IAB),
    ('7', '( ph -> ( X e. RR /\\ M e. RR ) )')])
HMA = '( ( D e. RR /\\ 1 < D ) /\\ ( C : NN --> CC /\\ S e. CC ) )'
st('ld2macn', '( %s -> ( u e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (HMA, MA('u')))
st('ld2licl', '( ( %s /\\ H e. RR+ ) -> ( ( u e. %s |-> %s ) e. L^1 /\\ %s = ( _i x. %s ) ) )'
   % (A7C, IOH('H'), GRHV('u'), LIH('H'), ITG(IOH('H'), GRHV('u'), 'u')))
st('ld2ptw', '( ( %s /\\ U e. RR ) -> ( abs ` %s ) <_ ( %s x. ( %s x. %s ) ) )' % (HP6, GRHV('U'), KC, WT('U'), MA('U')))
st('ld2li', '( ( %s /\\ H e. RR+ ) -> ( abs ` %s ) <_ ( %s x. %s ) )' % (HP6, LIH('H'), KC, ITG(IOH('H'), '( %s x. %s )' % (WT('u'), MA('u')), 'u')))
I2 = lambda H, Z=None: ITG(IOH(H), '( %s x. ( %s ^ 2 ) )' % (WT('u'), MA('u') if Z is None else MAK(Z, 'u')), 'u')
st('ld2sq1', '( ( %s /\\ H e. RR+ ) -> ( ( abs ` %s ) ^ 2 ) <_ ( ( %s ^ 2 ) x. ( 4 x. %s ) ) )' % (HP6, LIH('H'), KC, I2('H')))
st('ld2vlcv', '( %s -> %s ~~>r %s )' % (A7C, VLFH, VLH))
HMR = '( ( ( D e. RR /\\ 1 < D ) /\\ ( N e. NN /\\ X e. %s ) ) /\\ ( S e. CC /\\ U e. RR ) )' % DB()
st('ld2mrds', '( %s -> %s = %s )' % (HMR, subst(MRU('U'), {'C': CX()}), DSX('X', '( ( Im ` S ) + U )')))
st('ld2mmass', '( %s -> %s <_ ( 2 x. ( ( log ` D ) ^ 3 ) ) )' % (HZH, SLA))
st('ld2hp6', '( ( %s /\\ Z e. F ) -> %s )' % (HFAM, HP6K('Z')))
SQM = lambda U: 'sum_ r e. F ( %s ^ 2 )' % MAK('r', U)
st('ld2mvu', '( ( %s /\\ U e. RR ) -> %s <_ ( ( ; ; 4 0 0 x. %s ) x. ( 3 + ( abs ` U ) ) ) )' % (HFAM, SQM('U'), LOG3))
st('ld2mvw', '( ( %s /\\ U e. RR ) -> ( %s x. %s ) <_ ( ( ; ; ; 1 6 0 0 x. %s ) x. %s ) )' % (HFAM, WT('U'), SQM('U'), LOG3, WT4('U')))
st('ld2int', '( ( %s /\\ H e. RR+ ) -> sum_ r e. F %s <_ ( ; ; ; ; 1 2 8 0 0 x. %s ) )' % (HFAM, I2('H', 'r'), LOG3))
st('ld2trs', '( ( %s /\\ H e. RR+ ) -> sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ %s )' % (HFAM, LIK('r', 'H'), BV))
st('ld2lim', '( %s -> sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ %s )' % (HFAM, VLK('r'), BV))
st('ld2cexp', '( ( ( D e. RR /\\ 1 < D ) /\\ T e. RR ) -> ( ( ( ( D ^c ( ; ; 2 0 1 / ; ; 8 0 0 ) ) ^ 2 ) x. D ) x. ( %s ^ 2 ) ) <_ ( D ^c %s ) )' % (YPT, EXP2))
st('ld2num', '( ( %s /\\ T e. RR ) -> ( ( 1 / ; 3 6 ) x. %s ) <_ %s )' % (HZH, BV, FINAL))
st('ld2ssq', '( %s -> sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ %s )' % (HFAM, ECTRK('r'), FINAL))


# ------------------------------------------------------------------ grammar check
def gramcheck(labels):
    out = {}
    for lab in labels:
        p = os.path.join('worksheets', 'ld2g_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ld2g_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('h%s::ld2g_%s.%s |- %s\n' % (n, lab, n, h))
            f.write('qed::ax-1 |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower() or 'parse' in l.lower()]
        os.remove(p)
    return out


# ------------------------------------------------------------------ worksheet helpers (shared modules imported, never edited)
from mvlib import (dst, a1, ap, parts, J, eqt, eqc, body, fvmd, qedlast, _lhs_rhs, W, Closure, ClosureError, lift,
                   formula_of, strip_ante, split_imp, linarith, nlinarith, lineq, ringeq, ringeqp, ltle, checkrefs, mboxrefs, CN)
from ld1lib import hzh, dpos, basecl, lemul
from dshlib import z6stmt


def _stmt(lab):
    if lab in STATEMENTS:
        return STATEMENTS[lab]
    if lab in LD1S:
        return LD1S[lab]
    import dshlib
    if lab in dshlib.STATEMENTS:
        return dshlib.STATEMENTS[lab]
    return ' '.join(z6stmt(lab).split())


def concl(lab):
    return split_imp(_stmt(lab))[1]


def ante(lab):
    return split_imp(_stmt(lab))[0]


def cxval(w, An, nstep, X='X'):
    """( An -> ( CX(X) ` n ) = CHV(X, n) ) for the step nstep: ( An -> n e. NN )"""
    ex = a1(w, An, 'fvex', '%s e. _V' % CHV(X, 'n'))
    return fvmd(w, An, 'a', 'NN', CHV(X, 'a'), 'n', nstep, ex)
from z4blib import fvm2
import lin as _lin
_lin.FASTPATH = True
import num


def hyps(w, lab):
    """the $e hypotheses of LAB as worksheet steps h1, h2, ...; returns their names"""
    out = []
    for n, f in HYPS.get(lab, []):
        out.append(w.s([], '%s.%s' % (lab, n), f, name='h' + n))
    return out


def go(w, only=()):
    """assert the last line is the frozen statement, refuse unknown or mathbox labels, add"""
    if only and w.label not in only:
        return True
    last = w.lines[-1].split('|- ', 1)[1]
    assert last == STATEMENTS[w.label], '\n%s\n%s' % (last, STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); w.write(); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def fin(w):
    qedlast(w)
    return go(w)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])


# ------------------------------------------------------------------ section 6 shared helpers
from ld1_d import setupx, hab, basefacts, liftcl, termcl


def inst_forall(w, A, step, var, body_, val, valin):
    """( A -> body[var := val] ) from step ( A -> A. var e. CC body ) and valin ( A -> val e. CC ); returns (step, new body)"""
    cg, new = w.wcongr(body_, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    return w.s([cg, step, valin], 'rspcdva', '( %s -> %s )' % (A, new)), new


def a7parts(w, A, P, c):
    """the pieces of A7C (a conjunct of A) as steps under A, with the R = 1 form of DSH's antecedent"""
    F = {}
    F['hz'] = P[HZH]; F['nN'] = P['N e. NN']; F['cf'] = P['C : NN --> CC']; F['cb'] = P[CB]
    F['cfn'] = J(w, A, F['cf'], F['cb'])
    F['sr'] = P[SRNGH]; F['sc'] = P['S e. CC']; F['sne'] = P['S =/= 1']; F['lif'] = P[LIF]; F['es0'] = P['( E ` S ) = 0']
    F['lo'] = P['( ; 3 9 / ; 5 0 ) <_ ( Re ` S )']; F['re1'] = P['( Re ` S ) <_ 1']
    F['ecn'] = P['E e. ( %s -cn-> CC )' % HPZ]; F['cvx'] = P[CVXH]
    one = a1(w, A, '1nn', '1 e. NN'); mu = a1(w, A, 'sqf1', '( mmu ` 1 ) =/= 0')
    F['a7r'] = J(w, A, J(w, A, J(w, A, F['hz'], F['nN']), J(w, A, J(w, A, F['cfn'], J(w, A, one, mu)), J(w, A, F['sr'], F['sne']))), J(w, A, F['lif'], F['es0']))
    F['hlr'] = c.mem(HL, 'RR')
    c.have(HL, 'RR', F['hlr'])
    return F


def grcn1(w, A, F):
    """( A -> GRH e. ( DS -cn-> CC ) ) by dshgrcn at R = 1"""
    hyp = J(w, A, J(w, A, F['hz'], F['nN']), J(w, A, J(w, A, F['cf'], a1(w, A, '1nn', '1 e. NN')), J(w, A, F['sc'], F['ecn'])))
    return ap(w, A, 'dshgrcn', [hyp], '%s e. ( %s -cn-> CC )' % (GRH, Z6.DS))


SD1 = subst(concl('dshgrsd'), {'R': '1'})
SM1 = subst(concl('dshgrmaj'), {'R': '1'})
Y5 = '( ( abs ` ( Im ` S ) ) + 1 )'
M5 = split_imp(SM1[len('A. z e. CC '):])[1].rsplit(' <_ ', 1)[1].rsplit(' x. ( 2 ^c', 1)[0][1:].strip()


def hlu_ds(w, A, F, V, vr):
    """( A -> HLU(V) e. DS ) for a real V (step vr: ( A -> V e. RR )) from dshgrsd at R = 1"""
    gsd = ap(w, A, 'dshgrsd', [F['a7r']], SD1)
    Z = HLU(V)
    zc = dst(w, A, [dst(w, A, [F['hlr']], 'recnd', '%s e. CC' % HL), dst(w, A, [a1(w, A, 'ax-icn', '_i e. CC'), dst(w, A, [vr], 'recnd', '%s e. CC' % V)], 'mulcld', '( _i x. %s ) e. CC' % V)], 'addcld', '%s e. CC' % Z)
    rez = dst(w, A, [F['hlr'], vr], 'crred', '( Re ` %s ) = %s' % (Z, HL))
    imz = dst(w, A, [F['hlr'], vr], 'crimd', '( Im ` %s ) = %s' % (Z, V))
    c0 = Closure(w, A, {HL: ('RR', F['hlr']), '( Re ` S )': ('RR', dst(w, A, [F['sc']], 'recld', '( Re ` S ) e. RR'))})
    c0.atom('( Re ` S )')
    hl3 = linarith(w, A, [F['lo']], '%s <_ 3' % HL, closure=c0)
    le1 = dst(w, A, [F['hlr'], eqc(w, A, rez)], 'eqled', '%s <_ ( Re ` %s )' % (HL, Z))
    le3 = dst(w, A, [rez, hl3], 'eqbrtrd', '( Re ` %s ) <_ 3' % Z)
    D1 = '( ( Re ` %s ) = %s \\/ ( Re ` %s ) = 3 )' % (Z, HL, Z)
    dis = dst(w, A, [dst(w, A, [rez], 'orcd', D1)], 'orcd', '( %s \\/ %s <_ ( abs ` ( Im ` %s ) ) )' % (D1, Y5, Z))
    ins, new = inst_forall(w, A, gsd, 'z', SD1[len('A. z e. CC '):], Z, zc)
    return dst(w, A, [J(w, A, J(w, A, le1, le3), dis), ins], 'mpd', '%s e. %s' % (Z, Z6.DS)), zc, rez, imz


def pow10_8(w):
    """closed step ( 10 ^ 8 ) = 100000000"""
    ten = '; 1 0'
    e1 = w.s([num.fact(w, ten, 'CC'), w.inst('exp1')], 'ax-mp', '( %s ^ 1 ) = %s' % (ten, ten))
    tn = num.fact(w, ten, 'NN0')
    e2 = w.s([tn, num.fact(w, '1', 'NN0'), w.s([], '2t1e2', '( 2 x. 1 ) = 2'), e1, num.mul_lits(w, ten, ten)], 'numexp2x', '( %s ^ 2 ) = ; ; 1 0 0' % ten)
    e4 = w.s([tn, num.fact(w, '2', 'NN0'), w.s([], '2t2e4', '( 2 x. 2 ) = 4'), e2, num.mul_lits(w, '; ; 1 0 0', '; ; 1 0 0')], 'numexp2x', '( %s ^ 4 ) = ; ; ; ; 1 0 0 0 0' % ten)
    e8 = w.s([tn, num.fact(w, '4', 'NN0'), num.mul_lits(w, '2', '4'), e4, num.mul_lits(w, '; ; ; ; 1 0 0 0 0', '; ; ; ; 1 0 0 0 0')], 'numexp2x', '( %s ^ 8 ) = ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0' % ten)
    return e8


def ctau_nn(w, A):
    """( A -> CTau e. NN ) from df-ctau"""
    ct1 = w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')
    e800 = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    ctn = w.s([w.s([], '2nn', '2 e. NN'), w.s([e800], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. NN')
    return w.s([w.s([ct1, ctn], 'eqeltri', 'CTau e. NN')], 'a1i', '( %s -> CTau e. NN )' % A)


D8 = '( D ^c ( ; ; 2 0 1 / ; ; 8 0 0 ) )'


def kcfacts(w, A, c, F, tr):
    """leaves for KC's factors under A (c knows D, log D, YP; tr: ( A -> T e. RR )); returns the KC e. RR step"""
    c.leaf('CTau', 'NN', ctau_nn(w, A))
    c.leaf(P8, 'NN', w.s([w.s([w.s([], '10nn', '; 1 0 e. NN'), w.s([], '8nn0', '8 e. NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % P8)], 'a1i', '( %s -> %s e. NN )' % (A, P8)))
    c.leaf('T', 'RR', tr)
    c.leaf(D8, 'RR+', dst(w, A, [c.mem('D', 'RR+'), c.mem('( ; ; 2 0 1 / ; ; 8 0 0 )', 'RR')], 'rpcxpcld', '%s e. RR+' % D8))
    c.leaf(YPT, 'RR+', dst(w, A, [c.mem(YP, 'RR+'), c.mem('( ( 1 / 2 ) - T )', 'RR')], 'rpcxpcld', '%s e. RR+' % YPT))
    c.leaf(LOGD, 'ge0', linarith(w, A, [F['dl']], '0 <_ %s' % LOGD, closure=c))
    return c.mem(KC, 'RR')
