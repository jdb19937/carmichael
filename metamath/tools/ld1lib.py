"""Sortie LD1 helpers (Route Z: LoggedDetector.lean 121-1323, the first half).

STATEMENTS / HYPS / ORDER are the frozen statements of LD1-HANDOFF.md, one place;
`MM_DB=sorties/ld1.mm python3 tools/ld1lib.py [LABEL...]` grammar-checks them through mmatch.

Objects (written-out classes, no df-; the LoggedParams macros come from tools/dshlib.py):
  YP = Ypar D, NMAX = Nmax D, JPAR = Jpar D, BLK(j) = blockRange D j, COEFF(j,k,n,T) = coeffJK D T j k n,
  TT(n)      = truncTerm chi D S n            (character C : NN --> CC, |C| <_ 1: CFN)
  TRUNC      = sum_ n e. ( 1 ... NMAX ) TT(n) (the truncation of L1.c)
  BLKSUM(j)  = blockSum chi D S j             (S_j)
  TAYSUM(j,k,G,T) = taylorSum chi D T G j k   (T_{j,k} over ( 1 ... NMAX ))
  TWIST(j,k,G,T)  = the same sum over BLK(j)  (LoggedDensity twistSum, LD2's headline range)
  TREM(E,B,J,n)   = taylorRem E B J n,  REMTERM(j,n) = remTerm chi D T S j n,  REMSUM(j) = remSum chi D T S j
  TAU(n)     = ( # ` { x e. NN | x || n } )   (n.divisors.card)
Letters: sums bind n (integers), k (Taylor index), m (block index), d (divisor sums); x in TAU;
j in CFN's quantifier; s in CVXH's; p in the omega count.  Class variables: D N C S T (sigma)
J (a block index) K (a Taylor index) G (an imaginary part) E B X A U Z.
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dshlib import YP, YPF, NMAX, NMAXF, JPAR, JPARF, BLK, COEFF, HL, HZH, SRNGH, FDVH, EPH, ECTRH, A7H, PRN
from z5clib import HAB0, CFN, CB
import z6alib as Z6

STATEMENTS = {}
HYPS = {}
ORDER = []


def st(label, text, hyps=()):
    STATEMENTS[label] = ' '.join(text.split())
    HYPS[label] = list(hyps)
    ORDER.append(label)


# ------------------------------------------------------------------ notation
LOGD = '( log ` D )'
HZ2 = '( D e. RR /\\ 1 < D /\\ 2 <_ ( log ` D ) )'                       # Z5a's HZ2
HDN = Z6.HDN                                                               # ( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ D
CVXH = Z6.CVXH                                                             # the convexity bound for E (the L-function interface)
DV = lambda n: '{ x e. NN | x || %s }' % n
TAU = lambda n: '( # ` %s )' % DV(n)
BVA = lambda n: '( ( D bvA ( 2 x. D ) ) ` %s )' % n
EXY = lambda n: '( exp ` ( -u %s / %s ) )' % (n, YP)
NEX = lambda n, G: '( exp ` ( _i x. ( -u ( log ` %s ) x. %s ) ) )' % (n, G)   # MV's frequency form
NB = lambda j: '( ( 2 ^ %s ) x. D )' % j
BLKC = lambda j, n: '( %s < %s /\\ %s <_ ( ( 2 ^ ( %s + 1 ) ) x. D ) )' % (NB(j), n, n, j)
BODY = lambda n: '( ( ( %s x. %s ) x. ( C ` %s ) ) x. ( %s ^c -u S ) )' % (BVA(n), EXY(n), n, n)
TT = lambda n: 'if ( D < %s , %s , 0 )' % (n, BODY(n))
FZN = '( 1 ... %s )' % NMAX
TRUNC = 'sum_ n e. %s %s' % (FZN, TT('n'))
BLKSUM = lambda j: 'sum_ n e. %s if ( %s , %s , 0 )' % (FZN, BLKC(j, 'n'), BODY('n'))
TSUMMAND = lambda j, k, n, G, T='T': '( ( %s x. ( C ` %s ) ) x. %s )' % (COEFF(j, k, n, T), n, NEX(n, G))
TAYSUM = lambda j, k, G, T='T': 'sum_ n e. %s %s' % (FZN, TSUMMAND(j, k, 'n', G, T))
TWIST = lambda j, k, G, T='T': 'sum_ n e. %s %s' % (BLK(j), TSUMMAND(j, k, 'n', G, T))
LOGR = lambda n, B: '-u ( log ` ( %s / %s ) )' % (n, B)
TPOLY = lambda E, B, J, n: 'sum_ k e. ( 0 ... %s ) ( ( ( %s ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (J, E, LOGR(n, B))
TREM = lambda E, B, J, n: '( ( exp ` ( %s x. %s ) ) - %s )' % (E, LOGR(n, B), TPOLY(E, B, J, n))
DELTA = '( ( Re ` S ) - T )'
RBODY = lambda j, n: ('( ( ( ( ( %s x. %s ) x. ( %s ^c -u T ) ) x. %s ) x. ( C ` %s ) ) x. %s )'
                      % (BVA(n), EXY(n), n, TREM(DELTA, NB(j), JPAR, n), n, NEX(n, '( Im ` S )')))
REMTERM = lambda j, n: 'if ( %s , %s , 0 )' % (BLKC(j, n), RBODY(j, n))
REMSUM = lambda j: 'sum_ n e. %s %s' % (FZN, REMTERM(j, 'n'))
FIFTH = lambda J: '( ( 1 / 5 ) ^ ( %s + 1 ) )' % J
V4 = '( 1 / ( 4 x. %s ) )' % JPAR
V8 = '( 1 / ( ( 8 x. %s ) x. ( %s + 1 ) ) )' % (JPAR, JPAR)
KHALF = '( ( ; ; ; ; ; 6 0 0 0 0 0 x. CTau ) x. ( D ^c ( ; ; 2 0 1 / ; ; 8 0 0 ) ) )'
SIG = '( ( ( ; 3 9 / ; 5 0 ) <_ T /\\ T <_ 1 ) /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )'   # 39/50 <_ sigma <_ Re S <_ 1
HB = '( ( %s /\\ %s ) /\\ ( ( S e. CC /\\ T e. RR ) /\\ %s ) )' % (HZH, CFN, SIG)            # the block hypotheses
HA = '( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) )' % (HZH, CFN)   # the truncation hypotheses

# ------------------------------------------------------------------ section 0: parameter facts (antecedent HZH)
st('ld1d4', '( %s -> ( ( exp ` ; 4 0 ) <_ D /\\ 4 <_ D ) )' % HZH)
st('ld1yp', '( %s -> ( ( %s e. RR+ /\\ 1 < %s ) /\\ ( D <_ %s /\\ 4 <_ %s ) ) )' % (HZH, YP, YP, YP, YP))
st('ld1jpar', '( %s -> ( ( %s e. NN /\\ 3 <_ %s ) /\\ ( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) ) ) )'
   % (HZH, JPAR, JPAR, LOGD, JPAR, JPAR, LOGD, JPAR, LOGD))
st('ld1nmax', '( %s -> ( %s e. NN /\\ ( ( 8 x. %s ) x. %s ) <_ %s /\\ %s <_ ( ( ( 8 x. %s ) x. %s ) + 1 ) ) )'
   % (HZH, NMAX, YP, LOGD, NMAX, NMAX, YP, LOGD))
# the numeric clauses at x >_ 40 (Lean numeric_tail has 128; 256 here, see LD1-HANDOFF)
st('ld1ntail', '( ( X e. RR /\\ ; 4 0 <_ X ) -> ; ; 2 5 6 <_ ( exp ` ( ( ; 4 9 / ; 5 0 ) x. X ) ) )')
st('ld1nblk', '( ( X e. RR /\\ ; 4 0 <_ X ) -> ( 9 x. X ) <_ ( exp ` ( ( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 ) x. X ) ) )')
st('ld1ntay', '( ( X e. RR /\\ ; 4 0 <_ X ) -> ( ; 6 4 x. ( X ^ 2 ) ) <_ ( exp ` ( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. X ) ) )')

# ------------------------------------------------------------------ section 1: elementary
st('ld1bvatau', '( ( %s /\\ N e. NN ) -> ( abs ` ( ( A bvA B ) ` N ) ) <_ %s )' % (HAB0, TAU('N')))
st('ld1tau1', '( ( X e. RR /\\ 1 <_ X ) -> sum_ n e. ( 1 ... ( |_ ` X ) ) %s <_ ( X x. ( 1 + ( log ` X ) ) ) )' % TAU('n'))
st('ld1cpow', '( ( N e. NN /\\ S e. CC ) -> ( N ^c -u S ) = ( ( N ^c -u ( Re ` S ) ) x. %s ) )' % NEX('N', '( Im ` S )'))

# ------------------------------------------------------------------ section 2: Lemma 2.3 on Re Z = 1/2, and the Taylor remainder
st('ld1lhalf', '( ( ( %s /\\ ( N e. NN /\\ %s ) ) /\\ ( ( S e. CC /\\ Z e. CC ) /\\ ( ( Re ` Z ) = ( 1 / 2 ) /\\ %s ) ) ) -> '
   '( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) <_ ( %s x. ( %s x. ( ( 1 + ( abs ` ( ( Im ` Z ) - ( Im ` S ) ) ) ) ^ 2 ) ) ) )'
   % (HZ2, HDN, CVXH, KHALF, LOGD))
st('ld1tayrem', '( ( ( X e. RR /\\ ( abs ` X ) <_ ( 1 / 6 ) ) /\\ ( J e. NN0 /\\ 3 <_ J ) ) -> '
   '( abs ` ( ( exp ` X ) - sum_ k e. ( 0 ... J ) ( ( X ^ k ) / ( ! ` k ) ) ) ) <_ %s )' % FIFTH('J'))

# ------------------------------------------------------------------ section 3: L1.c, the truncation
st('ld1fdv', '( %s -> %s = sum_ n e. NN %s )' % (HA, FDVH, TT('n')))
st('ld1ttabs', '( ( %s /\\ K e. NN ) -> ( abs ` %s ) <_ ( K x. %s ) )' % (HA, TT('K'), EXY('K')))
st('ld1ttcvg', '( %s -> ( seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~> /\\ seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> ) )'
   % (HA, TT('n'), TT('n')))
st('ld1hexp', '( ( X e. RR /\\ 0 <_ X /\\ X <_ 1 ) -> ( X / 2 ) <_ ( 1 - ( exp ` -u X ) ) )')
st('ld1xexp', '( ( X e. RR /\\ 0 <_ X ) -> ( X x. ( exp ` -u X ) ) <_ 1 )')
TAILC = '( ( ; 3 2 x. ( %s ^ 2 ) ) x. ( exp ` ( -u 4 x. %s ) ) )' % (YP, LOGD)
Q4 = '( exp ` ( -u 1 / ( 4 x. %s ) ) )' % YP
st('ld1tailn', '( %s -> %s <_ ( 1 / 8 ) )' % (HZH, TAILC))
st('ld1tailpt', '( ( %s /\\ ( K e. NN /\\ ( %s + 1 ) <_ K ) ) -> ( abs ` %s ) <_ ( ( ( 4 x. %s ) x. ( exp ` ( -u 4 x. %s ) ) ) x. ( %s ^ K ) ) )'
   % (HA, NMAX, TT('K'), YP, LOGD, Q4))
st('ld1tailsum', '( %s -> ( abs ` sum_ n e. ( ZZ>= ` ( %s + 1 ) ) %s ) <_ %s )' % (HA, NMAX, TT('n'), TAILC))
st('ld1trunc', '( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ %s ) ) -> ( abs ` ( %s - %s ) ) <_ ( 1 / 8 ) )' % (HZH, CFN, SRNGH, FDVH, TRUNC))

# ------------------------------------------------------------------ section 4: dyadic blocks and the Taylor split
st('ld1ncov', '( %s -> %s <_ ( ( 2 ^ %s ) x. D ) )' % (HZH, NMAX, JPAR))
st('ld1exblk', '( ( ( D e. RR /\\ 0 < D ) /\\ ( N e. NN /\\ D < N ) /\\ ( J e. NN0 /\\ N <_ ( ( 2 ^ J ) x. D ) ) ) -> E. m e. ( 0 ..^ J ) %s )' % BLKC('m', 'N'))
st('ld1blku', '( ( ( ( D e. RR /\\ 0 < D ) /\\ N e. RR ) /\\ ( ( J e. NN0 /\\ K e. NN0 ) /\\ ( %s /\\ %s ) ) ) -> J = K )' % (BLKC('J', 'N'), BLKC('K', 'N')))
st('ld1sblk', '( ( ( %s /\\ %s ) /\\ S e. CC ) -> %s = sum_ m e. ( 0 ..^ %s ) %s )' % (HZH, CFN, TRUNC, JPAR, BLKSUM('m')))
st('ld1cjk0', '( -. %s -> %s = 0 )' % (BLKC('J', 'N'), COEFF('J', 'K', 'N')))
st('ld1cjk0n', '( ( ( D e. RR /\\ 0 < D ) /\\ ( J e. NN0 /\\ N e. NN ) /\\ -. N e. %s ) -> %s = 0 )' % (FZN, COEFF('J', 'K', 'N')))
st('ld1cjk0b', '( ( ( D e. RR /\\ 0 < D ) /\\ ( J e. NN0 /\\ N e. NN ) /\\ -. N e. %s ) -> %s = 0 )' % (BLK('J'), COEFF('J', 'K', 'N')))
st('ld1tayeq', '( ( ( %s /\\ %s ) /\\ ( ( J e. NN0 /\\ K e. NN0 ) /\\ ( G e. RR /\\ T e. RR ) ) ) -> %s = %s )'
   % (HZH, CFN, TAYSUM('J', 'K', 'G'), TWIST('J', 'K', 'G')))
st('ld1rpowtay', '( ( ( B e. RR+ /\\ N e. NN ) /\\ ( T e. RR /\\ E e. RR ) /\\ J e. NN0 ) -> '
   '( N ^c -u ( T + E ) ) = ( ( B ^c -u E ) x. ( ( N ^c -u T ) x. ( %s + %s ) ) ) )' % (TPOLY('E', 'B', 'J', 'N'), TREM('E', 'B', 'J', 'N')))
TAYK = lambda j: 'sum_ k e. ( 0 ... %s ) ( ( ( %s ^ k ) / ( ! ` k ) ) x. %s )' % (JPAR, DELTA, TAYSUM(j, 'k', '( Im ` S )'))
st('ld1blktay', '( ( ( %s /\\ %s ) /\\ ( ( S e. CC /\\ T e. RR ) /\\ J e. NN0 ) ) -> %s = ( ( %s ^c -u %s ) x. ( %s + %s ) ) )'
   % (HZH, CFN, BLKSUM('J'), NB('J'), DELTA, TAYK('J'), REMSUM('J')))
st('ld1blkabs', '( ( ( %s /\\ %s ) /\\ ( ( S e. CC /\\ T e. RR ) /\\ ( ( 0 <_ T /\\ T <_ ( Re ` S ) ) /\\ ( Re ` S ) <_ 1 ) ) /\\ J e. NN0 ) -> '
   '( abs ` %s ) <_ ( sum_ k e. ( 0 ... %s ) ( abs ` %s ) + ( abs ` %s ) ) )'
   % (HZH, CFN, BLKSUM('J'), JPAR, TAYSUM('J', 'k', '( Im ` S )'), REMSUM('J')))
st('ld1tremabs', '( ( ( E e. RR /\\ 0 <_ E /\\ E <_ ( ; 1 1 / ; 5 0 ) ) /\\ ( B e. RR+ /\\ ( N e. NN /\\ B < N /\\ N <_ ( 2 x. B ) ) ) /\\ ( J e. NN0 /\\ 3 <_ J ) ) -> '
   '( abs ` %s ) <_ %s )' % (TREM('E', 'B', 'J', 'N'), FIFTH('J')))
st('ld1rtabs', '( ( ( %s /\\ %s ) /\\ ( ( S e. CC /\\ T e. RR ) /\\ ( ( 0 <_ T /\\ T <_ ( Re ` S ) ) /\\ ( Re ` S ) <_ ( T + ( ; 1 1 / ; 5 0 ) ) ) ) /\\ ( J e. NN0 /\\ N e. NN ) ) -> '
   '( abs ` %s ) <_ if ( N <_ ( |_ ` ( 2 x. %s ) ) , ( ( %s x. ( %s ^c -u T ) ) x. %s ) , 0 ) )'
   % (HZH, CFN, REMTERM('J', 'N'), NB('J'), FIFTH(JPAR), NB('J'), TAU('N')))
st('ld1twoj', '( ( %s /\\ ( J e. NN0 /\\ J < %s ) ) -> ( ( 2 ^ J ) <_ ( D ^c ( 7 / ; 1 0 ) ) /\\ %s <_ ( D ^c ( ; 1 7 / ; 1 0 ) ) ) )' % (HZH, JPAR, NB('J')))
st('ld1fifth', '( %s -> %s <_ ( D ^c -u ( ; ; 1 1 2 / ; 8 1 ) ) )' % (HZH, FIFTH(JPAR)))
st('ld1remn', '( ( %s /\\ ( J e. NN0 /\\ J < %s ) /\\ ( T e. RR /\\ ( 3 / 4 ) <_ T /\\ T <_ 1 ) ) -> '
   '( %s x. ( ( %s ^c -u T ) x. ( ( 2 x. %s ) x. ( 1 + ( log ` ( 2 x. %s ) ) ) ) ) ) <_ ( 1 / ( 8 x. %s ) ) )'
   % (HZH, JPAR, FIFTH(JPAR), NB('J'), NB('J'), NB('J'), JPAR))
st('ld1rsabs', '( ( %s /\\ ( J e. NN0 /\\ J < %s ) ) -> ( abs ` %s ) <_ ( 1 / ( 8 x. %s ) ) )' % (HB, JPAR, REMSUM('J'), JPAR))

# ------------------------------------------------------------------ section 5: the pigeonholes
st('ld1pig', '( ( ( A e. Fin /\\ A =/= (/) ) /\\ ( X e. RR /\\ F : A --> RR ) /\\ ( ( # ` A ) x. X ) <_ sum_ k e. A ( F ` k ) ) -> E. k e. A X <_ ( F ` k ) )')
st('ld1exblkl', '( ( ( ( %s /\\ %s ) /\\ S e. CC ) /\\ ( 1 / 4 ) <_ ( abs ` %s ) ) -> E. m e. ( 0 ..^ %s ) %s <_ ( abs ` %s ) )'
   % (HZH, CFN, TRUNC, JPAR, V4, BLKSUM('m')))
st('ld1extay', '( ( ( %s /\\ ( J e. NN0 /\\ J < %s ) ) /\\ %s <_ ( abs ` %s ) ) -> E. k e. ( 0 ... %s ) %s <_ ( abs ` %s ) )'
   % (HB, JPAR, V4, BLKSUM('J'), JPAR, V8, TAYSUM('J', 'k', '( Im ` S )')))

# ------------------------------------------------------------------ section 6: the divisor-count mean square (LoggedDensity's coefficient mass)
st('ld1taumul', '( ( M e. NN /\\ N e. NN ) -> %s <_ ( %s x. %s ) )' % (TAU('( M x. N )'), TAU('M'), TAU('N')))
st('ld1taud', '( ( X e. RR /\\ 1 <_ X ) -> sum_ d e. ( 1 ... ( |_ ` X ) ) ( %s / d ) <_ ( ( 1 + ( log ` X ) ) ^ 2 ) )' % TAU('d'))
st('ld1tau2', '( ( X e. RR /\\ 1 <_ X ) -> sum_ n e. ( 1 ... ( |_ ` X ) ) ( %s ^ 2 ) <_ ( X x. ( ( 1 + ( log ` X ) ) ^ 3 ) ) )' % TAU('n'))


# ------------------------------------------------------------------ grammar check
def gramcheck(labels):
    out = {}
    for lab in labels:
        p = os.path.join('worksheets', 'ld1g_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ld1g_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('%s::? |- %s\n' % (n.split('.')[-1], h))
            f.write('qed::ax-1 |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower() or 'parse' in l.lower()]
        os.remove(p)
    return out


# ------------------------------------------------------------------ worksheet helpers (shared modules imported, never edited)
from mvlib import (dst, a1, ap, parts, J, eqt, eqc, body, fvmd, qedlast, _lhs_rhs, W, Closure, ClosureError, lift,
                   formula_of, strip_ante, split_imp, linarith, nlinarith, lineq, ringeq, ringeqp, ltle, checkrefs, mboxrefs)
import lin as _lin
_lin.FASTPATH = True
import num


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


def concl(lab):
    return split_imp(STATEMENTS[lab])[1]


def ante(lab):
    return split_imp(STATEMENTS[lab])[0]


def hzh(w, A, P=None):
    """the three HZH facts under A: (D e. RR, 1 < D, 40 <_ log D) steps; P = parts(w, A)"""
    P = P or parts(w, A)
    return P['D e. RR'], P['1 < D'], P['; 4 0 <_ ( log ` D )']


def dpos(w, A, dr, d1):
    """( A -> D e. RR+ ) and ( A -> 0 < D ) from D e. RR, 1 < D"""
    z = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A), a1(w, A, '1re', '1 e. RR'), dr, a1(w, A, '0lt1', '0 < 1'), d1], 'ltletrd' if False else 'lttrd',
             '( %s -> 0 < D )' % A)
    rp = w.s([dr, z], 'elrpd', '( %s -> D e. RR+ )' % A)
    return rp, z


def basecl(w, A, P=None):
    """a Closure under A that knows D (RR+, 1 < D), log D (RR, >_ 40), YP (RR+, 1 < YP, 4 <_ YP), NMAX, JPAR (NN),
    from the HZH conjuncts of A; returns (closure, dict of the named steps)"""
    P = P or parts(w, A)
    dr, d1, dl = hzh(w, A, P)
    rp, z = dpos(w, A, dr, d1)
    hz = P.get(HZH) or J(w, A, dr, d1, dl)
    yp = ap(w, A, 'ld1yp', [hz], concl('ld1yp'))
    yrp = dst(w, A, [dst(w, A, [yp], 'simpld', '( %s e. RR+ /\\ 1 < %s )' % (YP, YP))], 'simpld', '%s e. RR+' % YP)
    y1 = dst(w, A, [dst(w, A, [yp], 'simpld', '( %s e. RR+ /\\ 1 < %s )' % (YP, YP))], 'simprd', '1 < %s' % YP)
    y4 = dst(w, A, [dst(w, A, [yp], 'simprd', '( D <_ %s /\\ 4 <_ %s )' % (YP, YP))], 'simprd', '4 <_ %s' % YP)
    jp = ap(w, A, 'ld1jpar', [hz], concl('ld1jpar'))
    jn = dst(w, A, [dst(w, A, [jp], 'simpld', '( %s e. NN /\\ 3 <_ %s )' % (JPAR, JPAR))], 'simpld', '%s e. NN' % JPAR)
    nm = ap(w, A, 'ld1nmax', [hz], concl('ld1nmax'))
    nn = dst(w, A, [nm], 'simp1d', '%s e. NN' % NMAX)
    lr = dst(w, A, [rp], 'relogcld', '( log ` D ) e. RR')
    c = Closure(w, A, {'D': [('RR+', rp), ('gt1', d1)], '( log ` D )': [('RR', lr), ('ge1', None)] if False else ('RR', lr),
                       YP: [('RR+', yrp), ('gt1', y1)], JPAR: ('NN', jn), NMAX: ('NN', nn)})
    c.leaf(YP, 'RR+', yrp)
    return c, dict(dr=dr, d1=d1, dl=dl, rp=rp, z=z, hz=hz, yp=yp, yrp=yrp, y1=y1, y4=y4, jp=jp, jn=jn, nm=nm, nn=nn, lr=lr)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])


def lemul(w, A, c, step, C, side=2):
    """( A -> ( C x. X ) <_ ( C x. Y ) ) (side 2) or ( ( X x. C ) <_ ( Y x. C ) ) (side 1) from step ( A -> X <_ Y ),
    every hypothesis of lemul2ad / lemul1ad supplied through the closure c"""
    X, rel, Y = _lhs_rhs(body(w, step, A))
    assert rel == '<_', (X, rel, Y)
    hy = [c.mem(X, 'RR'), c.mem(Y, 'RR'), c.mem(C, 'RR'), c.ge0(C), step]
    if side == 2:
        return dst(w, A, hy, 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (C, X, C, Y))
    return dst(w, A, hy, 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (X, C, Y, C))
