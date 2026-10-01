"""Sortie EF3: helpers and the frozen statements (ExplicitFormula 2713-4131: the strip chain, the box zeros,
the weight lemma, the sigma pigeonhole, the left edge).  Built on tools/ef2lib.py.

    python3 tools/ef3lib.py print                                   # the frozen table
    MM_DB=sorties/ef3.mm python3 tools/ef3lib.py check [LABEL...]   # grammar check (mmatch)

Letters: the window/fibre/strip index is j (never k: LFN binds k), the integration variable is l,
the pigeonholed abscissa is a (LFN binds s); zeros q, filters p, ZS binds r, LDI binds u v, DD binds t x w.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from ef2lib import *
import ef2lib as _ef2
import zc1lib as _zc1
import c10lib as _c10


def stmt(label):
    """the assertion of LABEL from sorties/ef3.mm or carmichael.mm, without |-"""
    for fn in ('sorties/ef3.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def patch(*mods):
    for m in mods:
        m.stmt = stmt


patch(_ef2, _c10, _zc1)

# ---- objects -----------------------------------------------------------------------
LD0 = '{ v e. %s | ( F ` v ) =/= 0 }' % HP0
KS = '; ; ; ; ; ; 2 3 0 4 0 0 0'            # exists_good_sigma 2304000 (Lean 200000)
KMB = '; ; ; ; ; ; 1 5 3 6 0 0 0'           # the pigeonhole level 1536000 (internal)
KL = '; ; ; ; ; ; ; ; 5 0 0 0 0 0 0 0 0'     # left edge 500000000 (Lean 20000000)
KW = '; ; ; ; 2 4 0 0 0'                    # weight_sum_le 24000 (Lean 900)
KLD = '; ; ; ; ; ; ; 7 0 0 0 0 0 0 0'        # 4 x Landau 17500000


def BZ(F='F', U='U'):
    """Lean boxZeros f U: the zeros of F in [ 1/2 , 3/2 ] x [ -U , U ]"""
    return '{ r e. ( ( ( 1 / 2 ) + ( _i x. -u %s ) ) crect ( ( 3 / 2 ) + ( _i x. %s ) ) ) | ( %s ` r ) = 0 }' % (U, U, F)


def ZR(S_='S', C='C', L='L', H='H', F='F'):
    """the zeros of F strictly inside [ S , C ] x [ L , H ]"""
    return '{ p e. ( ( %s + ( _i x. %s ) ) crect ( %s + ( _i x. %s ) ) ) | ( ( %s ` p ) = 0 /\\ %s ) }' % (
        S_, L, C, H, F, SIN('p', S_, C, L, H))


def WQ(q='q', F='F'):
    return '( ( %s holord %s ) / ( 1 + ( abs ` ( Im ` %s ) ) ) )' % (F, q, q)


def RS(a, q='q'):
    """abs ( a - Re q ) ^ ( -1/2 )"""
    return '( ( abs ` ( %s - ( Re ` %s ) ) ) ^c -u ( 1 / 2 ) )' % (a, q)


def T0(j='j', P='P'):
    """the window centre P + j/2 + 1/4"""
    return '( ( %s + ( %s / 2 ) ) + ( 1 / 4 ) )' % (P, j)


def WLO(j='j', P='P'):
    return '( %s + ( %s / 2 ) )' % (P, j)


def WIN(j='j', P='P'):
    """the window ( P + j/2 , P + j/2 + 1/2 )"""
    return '( %s (,) ( %s + ( 1 / 2 ) ) )' % (WLO(j, P), WLO(j, P))


def ZK(j='j', P='P', F='F'):
    return ZS(F, T0(j, P))


def PHI(a, P='P', M='M', F='F'):
    """Lean's sigma functional: sum_j sum_{q in ZK(j)} w_q abs ( a - Re q ) ^ ( -1/2 )"""
    return 'sum_ j e. ( 0 ..^ %s ) sum_ q e. %s ( %s x. %s )' % (M, ZK('j', P, F), WQ('q', F), RS(a))


RSUM = lambda Y='Y': '( ( F holord q ) x. ( ( %s ^c q ) / q ) )' % Y
PT = lambda x, t: '( %s + ( _i x. %s ) )' % (x, t)
DDH = DD()
YH = '( Y e. RR /\\ 1 < Y )'
SGH = ('( ( T e. RR /\\ 2 <_ T ) /\\ ( P e. RR /\\ ( -u ( T + 1 ) <_ P /\\ P <_ 0 ) ) /\\ '
       '( M e. NN0 /\\ ( 0 <_ ( P + ( M / 2 ) ) /\\ ( P + ( M / 2 ) ) <_ ( T + 2 ) ) ) )')
LA = '( log ` ( A x. ( U + 2 ) ) )'

# ---- frozen statements ---------------------------------------------------------------
S = {}
# chain
S['ef3ldc'] = '( ( %s /\\ Y e. RR+ ) -> %s e. ( %s -cn-> CC ) )' % (HOLF('F', HP0), LDI(), LD0)
S['ef3vsp'] = ('( ( ( F e. ( D -cn-> CC ) /\\ ( ( P e. RR /\\ Q e. RR ) /\\ P <_ Q ) ) /\\ '
               '( ( L e. RR /\\ H e. RR /\\ M e. RR ) /\\ ( L <_ M /\\ M <_ H /\\ L < H ) ) /\\ '
               '( A. t e. ( L [,] H ) ( %s e. D /\\ %s e. D ) /\\ A. x e. ( P [,] Q ) ( %s e. D /\\ %s e. D /\\ %s e. D ) ) ) -> '
               '( F rectint <. %s , %s >. ) = ( ( F rectint <. %s , %s >. ) + ( F rectint <. %s , %s >. ) ) )') % (
    PT('P', 't'), PT('Q', 't'), PT('x', 'L'), PT('x', 'M'), PT('x', 'H'), PT('P', 'L'), PT('Q', 'H'), PT('P', 'L'), PT('Q', 'M'), PT('P', 'M'), PT('Q', 'H'))
SCH = ('( ( S e. RR /\\ C e. RR ) /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < C ) /\\ ( 1 < C /\\ C <_ ( 5 / 4 ) ) )')
GJ = lambda j: '( G ` %s )' % j
S['ef3chain'] = ('( ( ( %s /\\ %s /\\ %s ) /\\ ( ( M e. NN /\\ G : ( 0 ... M ) --> RR ) /\\ '
                 'A. j e. ( 0 ..^ M ) ( %s < %s /\\ ( %s - %s ) <_ 1 ) ) /\\ '
                 '( A. j e. ( 0 ... M ) A. x e. ( S [,] C ) ( F ` %s ) =/= 0 /\\ A. t e. ( %s [,] %s ) ( F ` %s ) =/= 0 ) ) -> '
                 '( %s rectint <. %s , %s >. ) = ( %s x. sum_ q e. %s %s ) )') % (
    DDH, YH, SCH, GJ('j'), GJ('( j + 1 )'), GJ('( j + 1 )'), GJ('j'), PT('x', GJ('j')), GJ('0'), GJ('M'), PT('S', 't'),
    LDI(), PT('S', GJ('0')), PT('C', GJ('M')), TPI, ZR('S', 'C', GJ('0'), GJ('M')), RSUM())
S['ef3zbz'] = ('( ( ( U e. RR /\\ ( L e. RR /\\ H e. RR ) ) /\\ ( ( S e. RR /\\ C e. RR ) /\\ ( ( 1 / 2 ) <_ S /\\ C <_ ( 3 / 2 ) ) ) /\\ '
               '( -u U <_ L /\\ H <_ U ) ) -> { p e. %s | %s } = %s )') % (BZ(), SIN('p'), ZR())
# box zeros
S['ef3bz'] = '( ( %s /\\ U e. RR ) -> ( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN ) )' % (DDH, BZ(), BZ())
# weight
S['ef3zw'] = '( ( ( %s /\\ T e. RR ) /\\ G C_ %s ) -> sum_ q e. G %s <_ ( ( ; ; ; 2 4 0 0 x. ( log ` %s ) ) / ( 1 + ( abs ` T ) ) ) )' % (
    DDH, ZS('F', 'T'), WQ(), XA())
S['ef3wt'] = '( ( ( %s /\\ ( U e. RR /\\ 2 <_ U ) ) /\\ G C_ %s ) -> sum_ q e. G %s <_ ( %s x. ( %s ^ 2 ) ) )' % (DDH, BZ(), WQ(), KW, LA)
# integrals over windows
S['ef3adj'] = ('( ( ( P e. RR /\\ M e. NN0 ) /\\ ( A. l e. ( P (,) ( P + ( M / 2 ) ) ) B e. CC /\\ ( l e. ( P (,) ( P + ( M / 2 ) ) ) |-> B ) e. L^1 ) ) -> '
               'S. ( P (,) ( P + ( M / 2 ) ) ) B _d l = sum_ j e. ( 0 ..^ M ) S. %s B _d l )') % WIN()
S['ef3hm'] = ('( ( ( P e. RR /\\ M e. NN0 /\\ W e. RR ) /\\ ( ( P <_ 0 /\\ 0 <_ ( P + ( M / 2 ) ) ) /\\ ( -u W <_ P /\\ ( P + ( M / 2 ) ) <_ W ) ) ) -> '
              'sum_ j e. ( 0 ..^ M ) ( 1 / ( 1 + ( abs ` %s ) ) ) <_ ( 5 x. ( log ` ( 1 + W ) ) ) )') % T0()
# sigma pigeonhole
S['ef3sig'] = ('( ( %s /\\ %s /\\ B e. Fin ) -> E. a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ( -. a e. B /\\ '
               '( A. j e. ( 0 ..^ M ) A. q e. %s ( Re ` q ) =/= a /\\ %s <_ ( %s x. ( %s ^ 2 ) ) ) ) )') % (
    DDH, SGH, ZK(), PHI('a'), KS, LT4)
# left edge
PHS = PT('S', 'l')
S['ef3vle'] = ('( ( ( G e. ( D -cn-> CC ) /\\ S e. RR ) /\\ ( ( P e. RR /\\ Q e. RR ) /\\ P < Q ) /\\ A. x e. ( P [,] Q ) %s e. D ) -> '
               '( ( l e. ( P (,) Q ) |-> ( abs ` ( G ` %s ) ) ) e. L^1 /\\ ( abs ` ( G lint <. %s , %s >. ) ) <_ S. ( P (,) Q ) ( abs ` ( G ` %s ) ) _d l ) )') % (
    PT('S', 'x'), PHS, PT('S', 'P'), PT('S', 'Q'), PHS)
SLH = '( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S <_ ( 5 / 8 ) ) )'
S['ef3left'] = ('( ( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ A. j e. ( 0 ..^ M ) A. q e. %s ( Re ` q ) =/= S ) /\\ '
                '( A. t e. ( P [,] ( P + ( M / 2 ) ) ) ( F ` %s ) =/= 0 /\\ %s <_ ( %s x. ( %s ^ 2 ) ) /\\ ( Q e. RR /\\ P < Q /\\ Q <_ ( P + ( M / 2 ) ) ) ) ) -> '
                '( abs ` ( %s lint <. %s , %s >. ) ) <_ ( ( %s x. ( Y ^c S ) ) x. ( %s ^ 2 ) ) )') % (
    DDH, YH, SGH, SLH, ZK(), PT('S', 't'), PHI('S'), KS, LT4, LDI(), PT('S', 'P'), PT('S', 'Q'), KL, LT4)

ORDER = list(S)


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'ef3gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'ef3gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ef3gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::ef3gc%s.1 |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in ORDER:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)


# ---- worksheet helpers -----------------------------------------------------------------
import lin as _lin
import cl as _cl
from cl import lift, Closure


def ringeq(w, ante, lhs, rhs, cl, name=None):
    """( ante -> lhs = rhs ) for polynomial expressions over CC (atoms from cl), by normal forms
    (tools/mvlib.py's ringeq without denominators)"""
    N = _lin.Normalizer(w, ante, cl)
    old = _lin.MAXDEG
    _lin.MAXDEG = max(old, 12)
    try:
        lv = tuple(set(cl.leaves) | set(cl.atoms))
        a, b = _lin.parse(lhs, True, lv), _lin.parse(rhs, True, lv)
        d = 1
        for q in list(_lin.denominators(a)) + list(_lin.denominators(b)):
            d = _lin.lcm(d, q)
        if d == 1:
            s1, v1 = N.nf(a, 1); s2, v2 = N.nf(b, 1)
            if v1.text() != v2.text():
                raise ValueError('ringeq: %s  vs  %s' % (v1.text(), v2.text()))
            return w.s([s1, s2], 'eqtr4d', '( %s -> %s = %s )' % (ante, lhs, rhs), name=name)
        from fractions import Fraction
        s1, v1 = N.nf(a, Fraction(d)); s2, v2 = N.nf(b, Fraction(d))
        if v1.text() != v2.text():
            raise ValueError('ringeq: %s  vs  %s' % (v1.text(), v2.text()))
        D = _lin.num.lit_text(Fraction(d))
        e = w.s([s1, s2], 'eqtr4d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ante, D, lhs, D, rhs))
        bi = w.s([cl.mem(lhs, 'CC'), cl.mem(rhs, 'CC'), cl.mem(D, 'CC'), cl.ne0(D)], 'mulcand',
                 '( %s -> ( ( %s x. %s ) = ( %s x. %s ) <-> %s = %s ) )' % (ante, D, lhs, D, rhs, lhs, rhs))
        return w.s([e, bi], 'mpbid', '( %s -> %s = %s )' % (ante, lhs, rhs), name=name)
    finally:
        _lin.MAXDEG = old


def St(w, A):
    """step maker under antecedent A"""
    return lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)


def elrab_(w, x, X, body, y):
    """closed step ( y e. { x e. X | body } <-> ( y e. X /\\ body[x:=y] ) )"""
    eq, new = w.wcongr(body, {x: y}, '%s = %s' % (x, y), {x: w.s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))})
    return w.s([eq], 'elrab', '( %s e. { %s e. %s | %s } <-> ( %s e. %s /\\ %s ) )' % (y, x, X, body, y, X, new)), new


def conj_split(w, A, st, f=None):
    """list of steps ( A -> c_i ) for the top-level conjuncts of the body of step st"""
    if f is None:
        f = body_of(w, st)
    parts = top_and(f)
    if len(parts) == 2:
        return [w.s([st, w.inst(k)], 'syl', '( %s -> %s )' % (A, p)) for k, p in zip(('simpl', 'simpr'), parts)]
    if len(parts) == 3:
        return [w.s([st, w.inst(k)], 'syl', '( %s -> %s )' % (A, p)) for k, p in zip(('simp1', 'simp2', 'simp3'), parts)]
    return [st]
