"""Sortie LDEN helpers (Route Z: LoggedDensity.lean, 34 used declarations, ending in `loggedDensity`).

STATEMENTS / ORDER are the frozen statements of LDEN-HANDOFF.md, one place;
`MM_DB=sorties/lden.mm python3 tools/ldenlib.py [LABEL...]` grammar-checks them through mmatch,
`python3 tools/gen/lden_freeze.py` compares them with tools/zdilib.py's LOGGED and with the database.

Letters (REP's, tools/zrlib.py): N modulus, S sigma, T height, Y a set of characters, G the good class,
P a parity; DSC = N ( T + 2 ), LD = log DSC; the zero sets bind r (box), q (zero sums), v (filters),
p (repIndex), x (characters), u (zrcov's heights), z (goodHigh), e (the class fibres), c (the class
index); the family theorems bind a b (family quantifiers), q (the sub-families), i j (block and Taylor
index), n (twist sums, LD1/LD2's letter), d (the coefficient mapping), t w (LD2's contour integral).
LD2's D N V T become DSC, N, T, S here (token substitution).  The headline is stated in LOGGED's own
letters h w c k m v u y p o (tools/zdilib.py).
"""
import sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'gen'))
import zrlib as ZR
from zrlib import (LD, EX, BOXR, ZFX, ORDX, LCX, IDX, QP, CELL, RI, NX, TT, GX, SQ13, E1, ETA, HP0, HOLF, LT2,
                   tsub, ante_of, top_and, Ctx, lin8, run8, numst8, W, Closure, lift)
import ld2lib as L2
from ld2lib import (HZH, JPAR, NMAX, YP, LOGD, V8, COEFF, BLK, NEX, TWISTX, ECTRHX, ECTRK, CX, LFX, DB, CHV, FINAL, EXP2,
                    SEPY, PTS, KZ, YZ, subst, ctau_nn, pow10_8, ap, dst, J, parts, a1, eqt, eqc, body, fvmd, linarith,
                    nlinarith, ringeq, ringeqp, inst_forall, checkrefs, mboxrefs, lemul, basecl, hzh, dpos, ltle)
from ld1lib import NB, TAU
import zdilib
from t21alib import NCo
from cl import split_imp, formula_of, strip_ante
import lin as _lin
_lin.FASTPATH = True
import num

STATEMENTS = {}
ORDER = []


def st(label, text):
    STATEMENTS[label] = ' '.join(text.split())
    ORDER.append(label)


# ------------------------------------------------------------------ objects
DSC = '( N x. ( T + 2 ) )'
assert LD == '( log ` %s )' % DSC
ZG = '( 0g ` ( DChr ` N ) )'
HZD = tsub(HZH, {'D': DSC})                                   # HZH at D := N ( T + 2 )
JP = tsub(JPAR, {'D': DSC})                                   # Jpar D = ceil LD
assert JP == '( |^ ` %s )' % LD
V8D = tsub(V8, {'D': DSC})                                    # Vthr D
Q1 = '( %s + 1 )' % JP                                        # Q1 d t = ceil L + 1
CLS = lambda p: '( ( |_ ` ( ( 2nd ` %s ) / 2 ) ) mod %s )' % (p, Q1)   # cls d t p
GH = '{ g e. CC | %s <_ ( abs ` ( Im ` g ) ) }' % LD          # goodHigh L (binder g: ldenri carries $d G c e p v z)
HSCL = '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) )'
HSIG = '( S e. RR /\\ ( ( ; 3 9 / ; 5 0 ) <_ S /\\ S <_ 1 ) )'
H40 = '; 4 0 <_ %s' % LD
EXPS = '( ( ; ; 1 5 1 / ; 5 0 ) x. ( 1 - S ) )'
assert EXPS == tsub(EXP2, {'T': 'S'})
PW = '( %s ^c %s )' % (DSC, EXPS)
P10 = lambda k: '( ; 1 0 ^ %s )' % k
B2 = '( ( ( ( 2 x. %s ) x. ( CTau ^ 2 ) ) x. ( %s ^ ; 1 2 ) ) x. %s )' % (P10('; 2 6'), LD, PW)   # family_card_le's constant
C1 = lambda D='D': '( ( %s x. ( ( log ` %s ) ^ ; 1 0 ) ) x. ( %s ^c %s ) )' % (P10('; 1 0'), D, D, EXPS)   # classI_card_le's constant
FINALD = tsub(FINAL, {'D': DSC, 'T': 'S'})
RHS1 = '( ( ( ( 3 x. %s ) x. ( CTau ^ 2 ) ) x. %s ) x. ( %s ^ ; 1 4 ) )' % (P10('; 3 0'), PW, LD)
H0 = '( ( 6 x. %s ) x. ( CTau ^ 2 ) )' % P10('; 3 0')
RHSL = '( ( %s x. ( ( N x. T ) ^c %s ) ) x. ( %s ^ ; 1 4 ) )' % (H0, EXPS, LD)
ZCB = lambda x: 'sum_ q e. %s %s' % (ZFX(x), ORDX(x, 'q'))                    # zeroCountBox x S T
SUMALL = 'sum_ x e. %s %s' % (DB(), ZCB('x'))
SUMY = NCo('S', 'T', 'N')                                                      # the same sum in LOGGED's letters y p o
PTB = lambda Z: '( %s e. CC /\\ ( abs ` ( Im ` %s ) ) <_ T )' % (Z, Z)

# the family (Lean s, chi, rho with hrho, hsep; pointwise typing of the maps K, Y)
HFAMP = '( F e. Fin /\\ ( A. a e. F ( K ` a ) e. %s /\\ A. a e. F ( Y ` a ) e. CC ) )' % DB()
PTSB = tsub(PTS[len('A. a e. F '):], {'T': 'S', 'V': 'T'})
PTSL = 'A. a e. F ( %s /\\ ( ( K ` a ) = %s -> %s <_ ( abs ` ( Im ` ( Y ` a ) ) ) ) )' % (PTSB, ZG, LD)
HFL = '( ( ( %s /\\ %s ) /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (HSCL, H40, HSIG, HFAMP, PTSL, SEPY)
ECTRKD = lambda Z: tsub(ECTRK(Z), {'D': DSC})
assert 'T' not in ECTRK('q').split()
ECTRKC = lambda Z: tsub(ECTRKD(Z), {'a': 'c'})                                  # the character mapping's binder c (ld2ssq's a := c)
SII = '{ q e. F | ( 1 / 4 ) <_ ( abs ` %s ) }' % ECTRKC('q')
TWX = lambda i, j, G, X: tsub(TWISTX(i, j, G, 'S', X), {'D': DSC})           # twistSum DSC S i j X G, sum letter n
TWE = lambda i, j, G, X: tsub(TWX(i, j, G, X), {'n': 'e'})                 # the same with the sum letter e (LDEN's sub-families)
SJK = lambda i, j: '{ q e. F | %s <_ ( abs ` %s ) }' % (V8D, TWE(i, j, '( Im ` ( Y ` q ) )', '( K ` q )'))
RJ = '( 0 ..^ %s )' % JP
KJ = '( 0 ... %s )' % JP
UNION = 'U_ i e. %s U_ j e. %s %s' % (RJ, KJ, SJK('i', 'j'))
SUMJK = 'sum_ i e. %s sum_ j e. %s ( # ` %s )' % (RJ, KJ, SJK('i', 'j'))
FC = lambda c: '{ e e. %s | %s = %s }' % (RI('P'), CLS('e'), c)
RIO = lambda P: tsub(RI(P), {'r': 'o'})                                     # repIndex with the box binder o (for the family theorems' $d)
HGD = 'A. e e. %s ( ( 1st ` e ) = %s -> A. z e. %s %s <_ ( abs ` ( Im ` z ) ) )' % (RI('P'), ZG, CELL('( 1st ` e )', '( 2nd ` e )'), LD)
HREP = '( ( ( ( N e. NN /\\ Y C_ %s ) /\\ Y e. Fin ) /\\ ( %s /\\ ( ( T e. RR /\\ 2 <_ T ) /\\ %s ) ) ) /\\ %s )' % (DB(), HSIG, H40, HGD)
HDEN = '( N e. NN /\\ ( %s /\\ ( ( T e. RR /\\ 2 <_ T ) /\\ %s ) ) )' % (HSIG, H40)
HD0 = '( N e. NN /\\ ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) )' % HSIG
MJ = '( |^ ` ( ( 2 ^ ( J + 1 ) ) x. D ) )'
assert BLK('J') == '( 1 ... %s )' % MJ
RNGA = 'A. a e. F ( abs ` ( Im ` ( Y ` a ) ) ) <_ T'
LVA = 'A. a e. F %s <_ ( abs ` %s )' % (V8, TWISTX('J', 'I', '( Im ` ( Y ` a ) )', 'S', '( K ` a )'))
W8 = '( ( 8 x. %s ) x. ( %s + 1 ) )' % (JPAR, JPAR)
assert V8 == '( 1 / %s )' % W8
BIG = '( ( %s x. %s ) x. ( 2 x. ( ( 2 x. %s ) x. %s ) ) )' % ('; ; 8 0 0', LD, LD, B2)
LOW = '( ; ; ; ; 1 2 8 0 0 x. ( %s ^ 2 ) )' % LD
NOTGH = '{ v e. %s | -. v e. %s }' % (ZFX(ZG), GH)

# ------------------------------------------------------------------ the frozen statements (proof order)
st('ldensc', '( %s -> ( ( 0 <_ T /\\ ( %s e. RR /\\ 4 <_ %s ) ) /\\ ( ( %s e. RR /\\ 1 < %s ) /\\ ( ( N x. T ) <_ %s /\\ %s <_ ( 2 x. ( N x. T ) ) ) ) ) )'
   % (HSCL, DSC, DSC, LD, LD, DSC, DSC))
st('ldenhz', '( ( %s /\\ %s ) -> %s )' % (HSCL, H40, HZD))
st('ldenq1', '( ( N e. NN /\\ %s ) -> ( %s e. NN /\\ ( ( %s + 1 ) <_ %s /\\ %s <_ ( %s + 2 ) ) ) )' % (TT, Q1, LD, Q1, Q1, LD))
st('ldenmod', '( ( ( Q e. NN /\\ ( A e. NN0 /\\ B e. NN0 ) ) /\\ ( A < B /\\ ( ( A mod 2 ) = ( B mod 2 ) /\\ ( ( |_ ` ( A / 2 ) ) mod Q ) = ( ( |_ ` ( B / 2 ) ) mod Q ) ) ) ) -> ( 2 x. Q ) <_ ( B - A ) )')
st('ldenc2', '( ( ( N e. NN /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( %s + ( 2 x. %s ) ) <_ %s ) -> 1 <_ ( ( Im ` B ) - ( Im ` A ) ) )' % (TT, PTB('A'), PTB('B'), IDX('A'), Q1, IDX('B')))
st('ldenthin', '( ( ( ( ( N e. NN /\\ S e. RR ) /\\ %s ) /\\ ( Q e. %s /\\ R e. %s ) ) /\\ ( ( ( ( 1st ` Q ) = ( 1st ` R ) /\\ Q =/= R ) /\\ %s = %s ) /\\ ( A e. %s /\\ B e. %s ) ) ) -> '
   '1 <_ ( abs ` ( ( Im ` A ) - ( Im ` B ) ) ) )' % (TT, RI('P'), RI('P'), CLS('Q'), CLS('R'), CELL('( 1st ` Q )', '( 2nd ` Q )'), CELL('( 1st ` R )', '( 2nd ` R )')))
st('ldenrio', '%s = %s' % (RI('P'), RIO('P')))
st('ldenfib', '( ( Y e. Fin /\\ ( N e. NN /\\ %s ) ) -> ( # ` %s ) = sum_ c e. ( 0 ..^ %s ) ( # ` %s ) )' % (TT, RI('P'), Q1, FC('c')))
st('ldencj', '( ( ( ( D e. RR /\\ 0 < D ) /\\ ( S e. RR /\\ 0 <_ S ) ) /\\ ( ( J e. NN0 /\\ I e. NN0 ) /\\ N e. NN ) ) -> ( abs ` %s ) <_ ( %s x. ( %s ^c -u S ) ) )'
   % (COEFF('J', 'I', 'N', 'S'), TAU('N'), NB('J')))
st('ldencjs', '( ( ( ( D e. RR /\\ 0 < D ) /\\ ( S e. RR /\\ 0 <_ S ) ) /\\ ( ( J e. NN0 /\\ I e. NN0 ) /\\ M e. NN ) ) -> '
   'sum_ n e. ( 1 ... M ) ( ( abs ` %s ) ^ 2 ) <_ ( ( ( %s ^c -u S ) ^ 2 ) x. ( M x. ( ( 1 + ( log ` M ) ) ^ 3 ) ) ) )' % (COEFF('J', 'I', 'n', 'S'), NB('J')))
st('ldenrp', '( ( X e. RR+ /\\ S e. RR ) -> ( ( ( X ^c -u S ) ^ 2 ) x. ( X ^ 2 ) ) = ( X ^c ( 2 - ( 2 x. S ) ) ) )')
st('ldenblk', '( ( ( %s /\\ %s ) /\\ ( J e. NN0 /\\ %s < %s ) ) -> ( %s ^c ( 2 - ( 2 x. S ) ) ) <_ ( ( 9 x. %s ) x. ( D ^c %s ) ) )' % (HZH, HSIG, NB('J'), NMAX, NB('J'), LOGD, EXPS))
st('ldenv8', '( %s -> ( ( %s e. RR+ /\\ ( %s x. %s ) = 1 ) /\\ ( %s <_ ( ; 3 2 x. ( %s ^ 2 ) ) /\\ ( %s <_ ( 2 x. %s ) /\\ ( %s + 1 ) <_ ( 2 x. %s ) ) ) ) )'
   % (HZH, V8, V8, W8, W8, LOGD, JPAR, LOGD, JPAR, LOGD))
st('ldenlv', '( ( ( ( %s /\\ ( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) ) ) /\\ ( ( S e. RR /\\ 0 <_ S ) /\\ ( J e. NN0 /\\ I e. NN0 ) ) ) /\\ ( ( %s /\\ ( %s /\\ %s ) ) /\\ %s ) ) -> '
   '( ( # ` F ) x. ( %s ^ 2 ) ) <_ ( ( ( ; ; 3 0 0 x. ( ( 1 + ( log ` %s ) ) ^ 2 ) ) x. ( %s + ( N x. T ) ) ) x. sum_ n e. ( 1 ... %s ) ( ( abs ` %s ) ^ 2 ) ) )'
   % (HZH, HFAMP, RNGA, SEPY, LVA, V8, MJ, MJ, MJ, COEFF('J', 'I', 'n', 'S')))
st('ldenc1b', '( ( ( ( ( %s /\\ ( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) ) ) /\\ ( ( N x. T ) <_ D /\\ %s ) ) /\\ ( ( %s /\\ ( %s /\\ %s ) ) /\\ ( ( J e. NN0 /\\ J < %s ) /\\ ( I e. NN0 /\\ %s ) ) ) ) /\\ %s < %s ) -> ( # ` F ) <_ %s )'
   % (HZH, HSIG, HFAMP, RNGA, SEPY, JPAR, LVA, NB('J'), NMAX, C1()))
st('ldenc1', '( ( ( ( %s /\\ ( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) ) ) /\\ ( ( N x. T ) <_ D /\\ %s ) ) /\\ ( ( %s /\\ ( %s /\\ %s ) ) /\\ ( ( J e. NN0 /\\ J < %s ) /\\ ( I e. NN0 /\\ %s ) ) ) ) -> ( # ` F ) <_ %s )'
   % (HZH, HSIG, HFAMP, RNGA, SEPY, JPAR, LVA, C1()))
st('ldenhiu', '( ( A e. Fin /\\ A. x e. A ( F ` x ) e. Fin ) -> ( # ` U_ x e. A ( F ` x ) ) <_ sum_ x e. A ( # ` ( F ` x ) ) )')
st('ldencov', '( %s -> F C_ ( %s u. %s ) )' % (HFL, SII, UNION))
st('ldencnt', '( %s -> ( # ` F ) <_ ( ( # ` %s ) + %s ) )' % (HFL, SII, SUMJK))
st('ldenii', '( %s -> ( # ` %s ) <_ ( ; 1 6 x. %s ) )' % (HFL, SII, FINALD))
st('ldenci', '( %s -> %s <_ ( ( %s x. ( %s + 1 ) ) x. %s ) )' % (HFL, SUMJK, JP, JP, C1(DSC)))
st('ldenfam', '( %s -> ( # ` F ) <_ %s )' % (HFL, B2))
st('ldencls', '( %s -> ( # ` %s ) <_ %s )' % (HREP, FC('C'), B2))
st('ldenri', '( %s -> ( # ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (HREP, RI('P'), LD, B2))
st('ldenwin', '( ( ( ( S e. RR /\\ ( ; 3 9 / ; 5 0 ) <_ S ) /\\ ( T e. RR /\\ U e. RR ) ) /\\ ( ( E e. RR /\\ E <_ 1 ) /\\ ( V e. %s /\\ ( abs ` ( ( Im ` V ) - U ) ) <_ E ) ) ) -> ( V e. %s /\\ V e. %s ) )'
   % (BOXR, SQ13('U'), HP0))
HLC = lambda cond: '( ( ( %s /\\ %s ) /\\ ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) ) /\\ ( U e. RR /\\ ( abs ` U ) <_ T ) )' % (NX, cond, HSIG)
st('ldenlc1', '( %s -> %s <_ ( ; ; 8 0 0 x. %s ) )' % (HLC('X =/= %s' % ZG), LCX('X', 'U'), LD))
st('ldenlc0', '( %s -> %s <_ ( ; ; 8 0 0 x. %s ) )' % (HLC('X = %s' % ZG), LCX('X', 'U'), LD))
st('ldenlc', '( ( ( %s /\\ ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) ) /\\ ( U e. RR /\\ ( abs ` U ) <_ T ) ) -> %s <_ ( ; ; 8 0 0 x. %s ) )' % (NX, HSIG, LCX('X', 'U'), LD))
st('ldenlow', '( %s -> sum_ q e. %s %s <_ %s )' % (HDEN, NOTGH, ORDX(ZG, 'q'), LOW))
st('ldenin1', '( %s -> sum_ x e. ( %s \\ { %s } ) %s <_ %s )' % (HDEN, DB(), ZG, ZCB('x'), BIG))
st('ldenin0', '( %s -> %s <_ ( %s + %s ) )' % (HDEN, ZCB(ZG), BIG, LOW))
st('ldene40', '( exp ` ; 4 0 ) <_ %s' % P10('; 2 0'))
st('ldenlarge', '( %s -> %s <_ %s )' % (HDEN, SUMALL, RHS1))
st('ldensmall', '( ( N e. NN /\\ ( %s /\\ ( ( T e. RR /\\ 2 <_ T ) /\\ %s < ; 4 0 ) ) ) -> %s <_ %s )' % (HSIG, LD, SUMALL, RHS1))
st('ldenld', '( %s -> %s <_ %s )' % (HD0, SUMALL, RHS1))
st('ldenledg', '( %s -> %s <_ %s )' % (HD0, SUMALL, RHSL))
st('ldencbv', '%s = %s' % (SUMALL, SUMY))
st('loggeddensity', zdilib.LOGGED)


# ------------------------------------------------------------------ grammar check
def gramcheck(labels):
    out = {}
    d = os.path.join(HERE, '..', 'scratch', 'lden')
    os.makedirs(d, exist_ok=True)
    for lab in labels:
        p = os.path.join(d, 'gc_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ldeng%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::ldeng%s.x |- %s\n' % (lab, STATEMENTS[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = (r.returncode == 0 and 'rror' not in txt, txt[-500:])
    return out


def stmt(lab):
    """a frozen LDEN statement, else the database's (sortie file, then carmichael.mm)"""
    return STATEMENTS[lab] if lab in STATEMENTS else dbstmt(lab)


def concl(lab):
    return split_imp(stmt(lab))[1]


def ante(lab):
    return split_imp(stmt(lab))[0]


def dbstmt(lab):
    """the statement of LAB in the sortie file or carmichael.mm"""
    import re
    for fn in (os.environ.get('MM_DB', 'carmichael.mm'), 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if not os.path.exists(p):
            continue
        m = re.search(r'\s%s \$p \|- (.*?) \$=' % re.escape(lab), open(p).read(), re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(lab)


def go(w):
    """assert the last line is the frozen statement, refuse unknown or mathbox labels, add"""
    last = w.lines[-1].split('|- ', 1)[1]
    assert last == STATEMENTS[w.label], '\n%s\n%s' % (last, STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); w.write(); return False
    mb = mboxrefs(w)
    if mb:
        print('MATHBOX LABELS in %s: %s' % (w.label, mb)); w.write(); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def fin(w, step):
    """qed by idi from STEP (the frozen statement)"""
    w.qed([step], 'idi', STATEMENTS[w.label])
    return go(w)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    bad = 0
    for lab, (ok, txt) in r.items():
        print(lab, 'OK' if ok else 'FAIL')
        if not ok:
            bad += 1; print('   ', txt[-400:])
    print('grammar checked %d, failures %d' % (len(r), bad))
